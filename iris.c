#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include <capstone/capstone.h>
#include <keystone/keystone.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>

// IRIS - the Interative Re-writer and Instruction Substitutor
// implemented runtime decoding, data encryption, flattening, junk insertion, random labeling.

// Algo steps:
// 1. Read input assembly.
// 2. Extract .rodata data (like "Hello, IRIS!\n").
// 3. Double-encrypt data with:
//    - enc_data[i] = ((orig_data[i] ^ enc_key[i]) ^ master_key_byte_for_i)
//    we will simplify to a known formula but actually implement runtime decoding fully.
// 4. Insert a runtime decoder that:
//    - Uses mmap syscall to allocate a buffer.
//    - Decodes data byte-by-byte in a loop, restoring original message.
//    - Returns pointer in rax.
// 5. Replace original data references with a call to the decoder, store returned pointer in a register, then use that pointer.
// 6. Control-flow flatten, add junk code, rename labels randomly, expand instructions, etc.
// 7. Output final assembly with no readable strings, no stable patterns.
//
// Requirements: capstone, keystone to be installed
//
// After producing output.s, assemble and link:
// gcc -c output.s -o output.o
// gcc output.o -o output
// ./output
// Should print "Hello, IRIS!" and exit.
//
// Unusually very large and complex. It's a demonstration of concept.

// SECTOR 1 : Random and Utils
static char *random_label_name() {
    static const char charset[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    int len=8;
    char *buf=malloc(len+5);
    buf[0]='_';buf[1]='_';
    for(int i=0;i<len;i++){
        buf[i+2]=charset[rand()% (sizeof(charset)-1)];
    }
    buf[len+2]='_';buf[len+3]='_';buf[len+4]='\0';
    return buf;
}

static uint64_t random_key() {
    uint64_t k=0;
    for(int i=0;i<8;i++)
        k=(k<<8)|(rand()&0xFF);
    return k;
}

// SECTOR 2 : Data Structures
typedef struct {
    char *label;
    char *text;
    int is_instruction;
    int is_directive;
} Instruction;

typedef struct {
    int start_index;
    int end_index;
    char *name;
    int id;
    int *succ;
    int succ_count;
} BasicBlock;

typedef struct {
    BasicBlock *blocks;
    int block_count;
} CFG;

typedef struct {
    uint64_t value;
    uint64_t encrypted_value;
} Constant;

typedef struct {
    Instruction *ins;
    int count;
    CFG cfg;
    Constant *constants;
    int const_count;
    unsigned char *orig_data;
    size_t orig_data_size;
    unsigned char *enc_data;
    unsigned char *enc_key;
    size_t enc_data_size;
} Program;

// SECTOR 3 : Reading Input
static Instruction *read_instructions(const char *filename, int *count) {
    FILE *f = fopen(filename,"r");
    if(!f){perror("fopen");exit(1);}
    Instruction *list=NULL;int cap=0,cnt=0;
    char line[1024];
    while(fgets(line,sizeof(line),f)){
        char *p=line;
        while(*p && isspace((unsigned char)*p)) p++;
        if(*p=='\0' || *p=='\n') continue;
        char *end=p+strlen(p)-1;
        while(end>p && isspace((unsigned char)*end)){*end='\0';end--;}

        if(cnt>=cap){cap=cap?cap*2:128;list=realloc(list,sizeof(Instruction)*cap);}
        list[cnt].label=NULL;
        list[cnt].text=strdup(p);
        list[cnt].is_directive=0;
        list[cnt].is_instruction=0;
        if(strchr(list[cnt].text,':')){
            char *colon=strchr(list[cnt].text,':');
            *colon='\0';
            list[cnt].label=strdup(list[cnt].text);
            char *rest=colon+1;
            while(*rest && isspace((unsigned char)*rest)) rest++;
            free(list[cnt].text);
            list[cnt].text=strdup(rest);
        }
        if(list[cnt].text[0]=='.') list[cnt].is_directive=1;
        else if(strlen(list[cnt].text)>0) list[cnt].is_instruction=1;
        cnt++;
    }
    fclose(f);
    *count=cnt;
    return list;
}

// SECTOR 4 : CFG Construction
typedef struct {char* name;int index;} LabelMap;

static int is_jump_instr(const char*txt){
    if(strncmp(txt,"jmp",3)==0)return 1;
    if(txt[0]=='j' && strlen(txt)>1)return 1;
    return 0;
}
static int is_block_end(const char*txt){
    if(is_jump_instr(txt)) return 1;
    if(strncmp(txt,"ret",3)==0)return 1;
    if(strncmp(txt,"syscall",7)==0)return 1;
    return 0;
}

static int find_label_index(LabelMap*lm,int c,const char*n){
    for(int i=0;i<c;i++) if(strcmp(lm[i].name,n)==0)return lm[i].index;
    return -1;
}

static LabelMap *build_label_map(Instruction*ins,int count,int*lc){
    LabelMap*lm=NULL;int lm_count=0,lm_cap=0;
    for(int i=0;i<count;i++){
        if(ins[i].label){
            if(lm_count>=lm_cap){lm_cap=lm_cap?lm_cap*2:64;lm=realloc(lm,sizeof(LabelMap)*lm_cap);}
            lm[lm_count].name=strdup(ins[i].label);
            lm[lm_count].index=i;
            lm_count++;
        }
    }
    *lc=lm_count;
    return lm;
}

static CFG build_cfg(Instruction*ins,int count){
    int label_count;
    LabelMap*lm=build_label_map(ins,count,&label_count);

    int *block_starts=NULL;int bs_count=0,bs_cap=0;
    for(int i=0;i<count;i++){
        if(i==0||ins[i].label){
            if(bs_count>=bs_cap){bs_cap=bs_cap?bs_cap*2:16;block_starts=realloc(block_starts,sizeof(int)*bs_cap);}
            block_starts[bs_count++]=i;
        }
    }

    typedef struct{int start;int end;}BE;
    BE*blocks=NULL;int blk_count=0,blk_cap=0;
    for(int i=0;i<bs_count;i++){
        int start=block_starts[i];
        int end=(i+1<bs_count)?(block_starts[i+1]-1):(count-1);
        for(int k=start;k<=end;k++){
            if(is_block_end(ins[k].text)){end=k;break;}
        }
        if(blk_count>=blk_cap){blk_cap=blk_cap?blk_cap*2:16;blocks=realloc(blocks,sizeof(BE)*blk_cap);}
        blocks[blk_count].start=start;blocks[blk_count].end=end;blk_count++;
    }

    BasicBlock*BB=calloc(blk_count,sizeof(BasicBlock));
    for(int i=0;i<blk_count;i++){
        BB[i].start_index=blocks[i].start;BB[i].end_index=blocks[i].end;
        BB[i].id=i;
        if(ins[BB[i].start_index].label) BB[i].name=strdup(ins[BB[i].start_index].label);
        else {
            char buf[64];sprintf(buf,"placeholder_block_%d",i);
            BB[i].name=strdup(buf);
        }
        BB[i].succ=NULL;BB[i].succ_count=0;
        int last=BB[i].end_index;
        char*txt=ins[last].text;
        if(is_jump_instr(txt)){
            char *space=strchr(txt,' ');
            if(space){
                char *target=space+1;while(*target && isspace((unsigned char)*target))target++;
                int li=find_label_index(lm,label_count,target);
                if(li>=0){
                    int target_block=-1;
                    for(int u=0;u<blk_count;u++){
                        if(li>=BB[u].start_index && li<=BB[u].end_index){target_block=u;break;}
                    }
                    if(strncmp(txt,"jmp",3)==0){
                        BB[i].succ=malloc(sizeof(int));BB[i].succ[0]=target_block;BB[i].succ_count=1;
                    } else {
                        BB[i].succ=malloc(sizeof(int)*2);
                        BB[i].succ[0]=target_block;BB[i].succ_count=1;
                        int fall=BB[i].end_index+1;
                        for(int w=0;w<blk_count;w++){
                            if(fall>=BB[w].start_index && fall<=BB[w].end_index && w!=target_block){
                                BB[i].succ[BB[i].succ_count++]=w;break;
                            }
                        }
                    }
                }
            }
        } else if(!is_block_end(txt)){
            int fall=BB[i].end_index+1;
            for(int w=0;w<blk_count;w++){
                if(fall>=BB[w].start_index && fall<=BB[w].end_index){
                    BB[i].succ=malloc(sizeof(int));
                    BB[i].succ[0]=w;BB[i].succ_count=1;break;
                }
            }
        }
    }

    CFG cfg;cfg.blocks=BB;cfg.block_count=blk_count;
    for(int i=0;i<label_count;i++) free(lm[i].name);
    free(lm);free(blocks);free(block_starts);
    return cfg;
}

// SECTOR 5 : Data Extraction
static void extract_data(Program *P) {
    int rodata_index=-1;
    for(int i=0;i<P->count;i++){
        if(P->ins[i].is_directive && strstr(P->ins[i].text,".rodata")){
            rodata_index=i;break;
        }
    }
    if(rodata_index<0)return;
    unsigned char *data=NULL;int dcount=0,dcap=0;
    for(int i=rodata_index+1;i<P->count;i++){
        if(P->ins[i].label || (P->ins[i].is_directive && strstr(P->ins[i].text,"section "))) break;
        char *line=P->ins[i].text;
        if(strncmp(line,"msg:",4)==0 || strncmp(line,"db ",3)==0 || strstr(line,"db ")){
            // parse db line
            char *dbpos=strstr(line,"db ");
            if(!dbpos) {
                // maybe "msg:" line: after label might have db
                if(strchr(line,':')){
                    char *c=strchr(line,':');c++;
                    while(*c && isspace((unsigned char)*c))c++;
                    if(strncmp(c,"db ",3)==0) dbpos=c;
                }
            }
            if(dbpos) {
                char *args=dbpos+3;
                while(*args) {
                    while(*args && isspace((unsigned char)*args))args++;
                    if(*args=='"'){
                        args++;
                        while(*args && *args!='"'){
                            if(dcount>=dcap){dcap=dcap?dcap*2:64;data=realloc(data,dcap);}
                            data[dcount++]=(unsigned char)*args;
                            args++;
                        }
                        if(*args=='"')args++;
                    } else if(strncmp(args,"0x",2)==0){
                        char *endp;
                        unsigned long val=strtoul(args,&endp,16);
                        if(dcount>=dcap){dcap=dcap?dcap*2:64;data=realloc(data,dcap);}
                        data[dcount++]=(unsigned char)val;
                        args=endp;
                    } else {
                        if(*args && *args!=',' && *args!='\n') {
                            if(dcount>=dcap){dcap=dcap?dcap*2:64;data=realloc(data,dcap);}
                            data[dcount++]=(unsigned char)*args;
                            args++;
                        } else args++;
                    }
                    while(*args && (isspace((unsigned char)*args)||*args==','))args++;
                }
            }
        }
    }
    P->orig_data=data;P->orig_data_size=dcount;
}

// SECTOR 6 : Data Encryption
static void encrypt_data(Program *P) {
    if(P->orig_data_size==0)return;
    P->enc_data_size=P->orig_data_size;
    P->enc_data=malloc(P->enc_data_size);
    P->enc_key=malloc(P->enc_data_size);
    for(size_t i=0;i<P->enc_data_size;i++){
        P->enc_key[i]=(unsigned char)(rand()&0xFF);
    }
    // We'll have a master_key as a sequence of random bytes (8 bytes)
    uint64_t master_key=random_key();
    // enc_data[i] = (orig_data[i] ^ enc_key[i]) ^ ((master_key>>(8*(i%8)))&0xFF)
    // This ensures per-byte variation.
    for(size_t i=0;i<P->enc_data_size;i++){
        unsigned char mkb=((unsigned char*)&master_key)[i%8];
        unsigned char val = P->orig_data[i]^P->enc_key[i];
        val=val^mkb;
        P->enc_data[i]=val;
    }
    // We'll store master_key as well
    // because we kinda need them in insert_data_decoder
    // Actually, we do that later.
}

// SECTOR 7 : Constants Encryption (like mov rax,0x1234 etc, just thought of it and it sounds like a banger ngl)
static uint64_t random_key_val() {
    uint64_t val=0;
    for(int i=0;i<8;i++) val=(val<<8)|(rand()&0xFF);
    return val;
}

static void encrypt_constants(Program *P) {
    // same as previous approach:
    for(int i=0;i<P->count;i++){
        if(!P->ins[i].is_instruction) continue;
        char *t=P->ins[i].text;
        // If "mov rax,0x..."
        if(strncmp(t,"mov rax,",8)==0) {
            char *imm_str=t+8;
            while(*imm_str && isspace((unsigned char)*imm_str)) imm_str++;
            if(strncmp(imm_str,"0x",2)==0) {
                uint64_t val=strtoull(imm_str,NULL,16);
                uint64_t key=random_key_val();
                uint64_t enc=val^key;
                int cid=P->const_count;
                P->constants=realloc(P->constants,sizeof(Constant)*(cid+1));
                P->constants[cid].value=val;
                P->constants[cid].encrypted_value=enc;
                P->const_count++;
                free(P->ins[i].text);
                char buf[256];sprintf(buf,"mov rdi,%d\ncall decrypt_stub_constant",cid);
                P->ins[i].text=strdup(buf);
            }
        }
    }
}

// SECTOR 8 : Insert runtime decrypt stub for constants
static char *decrypt_stub_constant_label;
static void insert_runtime_decrypt_stub(Program *P) {
    decrypt_stub_constant_label = random_label_name();
    // decrypt_stub_constant:
    // rdi=cid
    // load enc and key arrays from memory (we'll do after code flatten).
    // for constants, we can store them similarly in rodata as pairs enc/key.
    // but since we only have a few constants, do a simple dq arrays at end:
    // We'll do same as before: val=enc^key, just store enc and key=val^enc.
    // already done. Just do:
    //   decrypt_stub_constant:
    //     mov rax,[rip+const_table_const+rdi*8]
    //     mov rcx,[rip+const_keys_const+rdi*8]
    //     xor rax,rcx
    //     ret

    char *table_label1=random_label_name();
    char *table_label2=random_label_name();
    P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+4));
    int idx=P->count;
    P->ins[idx].label=strdup(decrypt_stub_constant_label);P->ins[idx].text=strdup("mov rax,[rip+const_table_const+rdi*8]\nmov rcx,[rip+const_keys_const+rdi*8]\nxor rax,rcx\nret");
    P->ins[idx].is_instruction=1;P->ins[idx].is_directive=0;idx++;
    P->count=idx;

    // We'll append constants table at the end, but let's do after entire flattening.
    // but also need to just remember tables: const_table_const, const_keys_const.
    // we'll insert them at the very end after transformations.
}

// SECTOR 9 : Insert Data Decoder
// allocating a buffer using mmap (syscall) to store decoded data.
// then we will decode byte by byte: enc_data[i] = ((orig_data[i]^enc_key[i])^master_key_byte)
// but we also know that master_key_byte from the stored master_key (8 bytes).
// so we'll store master_key as 8 bytes, enc_data and enc_key arrays in rodata.
//
// need to produce code that:
// 1. mov rax,9 (syscall: mmap)
//   rdi=0, rsi=length, rdx=PROT_READ|PROT_WRITE=3, r10=MAP_PRIVATE|MAP_ANONYMOUS=0x22, r8=-1, r9=0
//   syscall -> rax=ptr
// 2. lea r11,[rip+enc_data], r12=[rip+enc_key], r13=[rip+master_key_label]
// 3. loop over length in rcx, decode each byte:
//   mov bl,[r11+r8]
//   xor bl,[r12+r8]
//   mov al,[r13+(r8%8)] (extract byte of master key)
//   xor bl,al
//   mov [rax+r8], bl
//   inc r8
//   loop
//4. return rax

static char *data_decoder_label;
static char *enc_data_label;
static char *enc_key_label;
static char *master_key_label;
static char *const_table_const_label;
static char *const_keys_const_label;
static uint64_t master_key_global;

static void insert_data_decoder(Program *P) {
    data_decoder_label=random_label_name();
    enc_data_label=random_label_name();
    enc_key_label=random_label_name();
    master_key_label=random_label_name();
    const_table_const_label=random_label_name();
    const_keys_const_label=random_label_name();

    master_key_global = random_key();

    // Remove original rodata lines with ASCII
    for(int i=0;i<P->count;i++){
        if(P->ins[i].is_directive && strstr(P->ins[i].text,".rodata")){
            // blank them out
            P->ins[i].text[0]='\0';
            for(int j=i+1;j<P->count;j++){
                if(P->ins[j].label || (P->ins[j].is_directive && strstr(P->ins[j].text,"section "))) break;
                P->ins[j].text[0]='\0';
                if(P->ins[j].label){free(P->ins[j].label);P->ins[j].label=NULL;}
            }
            break;
        }
    }

    // We'll append all data at the very end:
    // section .rodata
    // master_key_label: db 8 bytes of master_key_global
    // enc_data_label: db enc_data bytes
    // enc_key_label: db enc_key bytes
    // const_table_const_label, const_keys_const_label for constants if any

    // We'll insert them after finishing transformations, but let's do now for completeness:
    P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+ (int)(2*P->enc_data_size+P->const_count*2+50)));
    int idx=P->count;
    P->ins[idx].label=NULL;P->ins[idx].text=strdup("section .rodata");P->ins[idx].is_directive=1;P->ins[idx].is_instruction=0;idx++;

    // Master key:
    {
        char line[64];
        P->ins[idx].label=strdup(master_key_label);
        sprintf(line,"db 0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x",
                (unsigned)((master_key_global>>0)&0xFF),(unsigned)((master_key_global>>8)&0xFF),
                (unsigned)((master_key_global>>16)&0xFF),(unsigned)((master_key_global>>24)&0xFF),
                (unsigned)((master_key_global>>32)&0xFF),(unsigned)((master_key_global>>40)&0xFF),
                (unsigned)((master_key_global>>48)&0xFF),(unsigned)((master_key_global>>56)&0xFF));
        P->ins[idx].text=strdup(line);
        P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
    }

    P->ins[idx].label=strdup(enc_data_label);P->ins[idx].text=strdup("");P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
    for(size_t i=0;i<P->enc_data_size;i++){
        char b[32];sprintf(b,"db 0x%02x",(unsigned)P->enc_data[i]);
        P->ins[idx].label=NULL;P->ins[idx].text=strdup(b);
        P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
    }

    P->ins[idx].label=strdup(enc_key_label);P->ins[idx].text=strdup("");P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
    for(size_t i=0;i<P->enc_data_size;i++){
        char b[32];sprintf(b,"db 0x%02x",(unsigned)P->enc_key[i]);
        P->ins[idx].label=NULL;P->ins[idx].text=strdup(b);
        P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
    }

    // For constants:
    {
        P->ins[idx].label=strdup(const_table_const_label);P->ins[idx].text=strdup("");P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
        for(int i=0;i<P->const_count;i++){
            char buf[64];sprintf(buf,"dq 0x%lx",(unsigned long)P->constants[i].encrypted_value);
            P->ins[idx].label=NULL;P->ins[idx].text=strdup(buf);
            P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
        }
        P->ins[idx].label=strdup(const_keys_const_label);P->ins[idx].text=strdup("");P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
        for(int i=0;i<P->const_count;i++){
            uint64_t key = P->constants[i].value ^ P->constants[i].encrypted_value;
            char buf[64];sprintf(buf,"dq 0x%lx",(unsigned long)key);
            P->ins[idx].label=NULL;P->ins[idx].text=strdup(buf);
            P->ins[idx].is_directive=0;P->ins[idx].is_instruction=0;idx++;
        }
    }

    // Insert data_decoder:
    // data_decoder:
    //   ; rdx = length, we must know length. We'll store length in a label too.
    //   ; We'll store length in a label: <enc_data_label>_len:
    char *enc_data_len_label = random_label_name();
    P->ins[idx].label=strdup(enc_data_len_label);
    {
        char buf[64];sprintf(buf,"dq %zu",P->enc_data_size);
        P->ins[idx].text=strdup(buf);
        P->ins[idx].is_instruction=0;P->ins[idx].is_directive=0;idx++;
    }

    // data_decoder:
    // Steps:
    // 1. read length: mov rdx,[rip+enc_data_len_label]
    // 2. setup mmap syscall to allocate a buffer:
    //    rax=9 (mmap), rdi=0, rsi=length, rdx=PROT_READ|PROT_WRITE=3,
    //    r10=MAP_PRIVATE|MAP_ANONYMOUS=0x22, r8=-1, r9=0
    //    syscall
    //    rax=allocated_ptr
    //3. lea r11,[rip+enc_data_label], r12=[rip+enc_key_label], r13=[rip+master_key_label]
    //4. rcx=length, r8=0
    // decode_loop:
    //   mov bl,[r11+r8]
    //   xor bl,[r12+r8]
    //   ; get master_key byte:
    //   We do: mkb = ((master_key_global>>(8*(r8%8)))&0xFF)
    //   implement modulo by using and: r8%8 = r8 & 7
    //   shift master_key_label and load:
    //   but again we have master_key as 8 bytes in memory, so we can just do:
    //   mov al,[r13+(r8&7)] since we can do:
    //   and rdi,rdi not enough. we'll do:
    //   (use a small trick btw: r8&7 = r8 & 7 = r8 & 0b111 = r8 & 0x7)?????
    //   using a separate register: mov rax,r8; and rax,7; add r13,rax; mov al,[r13]; subtract back?
    //   let's do a small inline snippet
    //   we'll choose a simpler approach: pre-load master_key bytes into registers or do a jump table of sorts?
    //   well but due to complexity and no placeholders
    //   We'll just do:
    //   mov rax,r8
    //   and rax,7
    //   mov r15,r13
    //   add r15,rax
    //   mov al,[r15]
    //
    //   xor bl,al
    //   mov [rax+r8],bl
    //   inc r8
    //   loop decode_loop
    // ret with rax=decoded_ptr

    char *decoder_label = data_decoder_label;
    char *code=
    "section .text\n"
    "%s:\n" // decoder_label
    "mov rdx,[rip+" "%s" "]\n" // length
    "mov rax,9\n"   // mmap syscall
    "xor rdi,rdi\n"
    "mov rsi,rdx\n"
    "mov rdx,3\n"   // PROT_READ|PROT_WRITE
    "mov r10,0x22\n"// MAP_PRIVATE|MAP_ANONYMOUS
    "mov r8,-1\n"
    "mov r9,0\n"
    "syscall\n"
    "mov r14,rax\n"  // r14=decoded_ptr
    "lea r11,[rip+" "%s" "]\n" // enc_data
    "lea r12,[rip+" "%s" "]\n" // enc_key
    "lea r13,[rip+" "%s" "]\n" // master_key_label
    "mov rcx,rdx\n"
    "xor r8,r8\n"
    "decode_loop:\n"
    "mov bl,[r11+r8]\n"
    "xor bl,[r12+r8]\n"
    "mov rax,r8\n"
    "and rax,7\n"
    "mov r15,r13\n"
    "add r15,rax\n"
    "mov al,[r15]\n"
    "xor bl,al\n"
    "mov [r14+r8],bl\n"
    "inc r8\n"
    "loop decode_loop\n"
    "mov rax,r14\n"
    "ret\n";

    // insert code after current
    // format code with labels replaced:
    char final_code[4096];
    snprintf(final_code,sizeof(final_code),code,decoder_label,enc_data_len_label,enc_data_label,enc_key_label,master_key_label);

    // split the final_code by lines and insert into P->ins
    char *saveptr=NULL;
    char *linep=strtok_r(final_code,"\n",&saveptr);
    while(linep){
        Instruction I;
        I.label=NULL;
        char *cl=strchr(linep,':');
        if(cl && (cl-linep)>0 && *(cl+1)=='\0'){
            // label line
            int len=(int)(cl-linep);
            I.label=strndup(linep,len);
            I.text=strdup("");
            I.is_directive=0;I.is_instruction=0;
        } else {
            I.text=strdup(linep);
            I.is_directive=(linep[0]=='.');
            I.is_instruction=(strlen(linep)>0 && linep[0]!='.');
        }
        P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
        P->ins[P->count]=I;
        P->count++;
        linep=strtok_r(NULL,"\n",&saveptr);
    }
}

// SECTOR 10 : Flatten CFG

static void flatten_cfg(Program *P) {
    CFG *cfg = &P->cfg;

    // We'll produce a new list of instructions from scratch:
    Instruction *new_list = NULL;
    int new_count = 0, new_cap = 0;

    #define ADD_INST(LBL,TEXT) do { \
        if(new_count>=new_cap){new_cap=new_cap?new_cap*2:256;new_list=realloc(new_list,sizeof(Instruction)*new_cap);} \
        new_list[new_count].label=(LBL)?strdup(LBL):NULL; \
        new_list[new_count].text=strdup(TEXT); \
        new_list[new_count].is_directive=((TEXT[0]=='.')?1:0); \
        new_list[new_count].is_instruction=(!new_list[new_count].is_directive && strlen(TEXT)>0); \
        new_count++; \
    } while(0)

    // Add a global start if not present
    // Here, we assume code had a _start or main label. We'll unify entry at block 0
    // We'll insert:
    // .text
    // .global _start
    // _start:
    //    mov rbx,0
    //    jmp dispatcher

    // dispatcher:
    //   cmp rbx,0
    //   je block_0
    //   cmp rbx,1
    //   je block_1
    //   ...
    // If none matches, maybe jmp block_0 by default or ret?

    // Insert text section if not present:
    ADD_INST(NULL,".text");
    ADD_INST(NULL,".global _start");
    ADD_INST("_start","mov rbx,0\njmp dispatcher");

    // dispatcher:
    ADD_INST("dispatcher","");
    for (int i=0;i<cfg->block_count;i++) {
        char buf[128];
        sprintf(buf,"cmp rbx,%d",i);
        ADD_INST(NULL,buf);
        sprintf(buf,"je block_%d",i);
        ADD_INST(NULL,buf);
    }

    // Now each block:
    for (int i=0;i<cfg->block_count;i++){
        char block_label[64];sprintf(block_label,"block_%d",i);
        ADD_INST(block_label,"nop");

        // Copy original block instructions:
        // The original block i: from cfg->blocks[i].start_index to end_index
        for (int k=cfg->blocks[i].start_index; k<=cfg->blocks[i].end_index;k++){
            // If original had a label, skip it because we now have our own block label
            if (P->ins[k].label && strcmp(P->ins[k].label,block_label)==0) {
                if(strlen(P->ins[k].text)>0) ADD_INST(NULL,P->ins[k].text);
            } else {
                if(strlen(P->ins[k].text)>0) ADD_INST(NULL,P->ins[k].text);
            }
        }

        // If block has successors, pick the first successor as unconditional jump:
        // If multiple successors originally (conditional jump), we simplified by flattening to dispatcher logic.
        if(cfg->blocks[i].succ_count>0) {
            int next=cfg->blocks[i].succ[0];
            char buf[128];
            sprintf(buf,"mov rbx, %d",next);
            ADD_INST(NULL,buf);
            ADD_INST(NULL,"jmp dispatcher");
        } else {
            // terminal block: likely ends in ret/syscall already
            // no successor instructions needed
        }
    }

    // Replace P->ins with new_list
    for(int i=0;i<P->count;i++){
        free(P->ins[i].text);
        if(P->ins[i].label) free(P->ins[i].label);
    }
    free(P->ins);
    P->ins=new_list;
    P->count=new_count;

    // After flattening, all blocks are linearized, no direct label references remain except block_x and dispatcher.
}

// SECTOR 11 : Inter-procedural Obfuscation
static void inter_procedural_obfuscation(Program *P) {
    // Insert fake_func at the end
    char *fake_func_label = random_label_name();
    Instruction fake[] = {
        {strdup(fake_func_label),strdup("xor rcx,rcx\nadd rcx,0x9999\ninc rcx\nret"),1,0}
    };

    P->ins = realloc(P->ins, sizeof(Instruction)*(P->count+1));
    P->ins[P->count] = fake[0];
    P->count++;

    // Insert 'call fake_func' after dispatcher cmp/je pairs:
    // Find dispatcher label
    int disp_index=-1;
    for (int i=0;i<P->count;i++){
        if(P->ins[i].label && strcmp(P->ins[i].label,"dispatcher")==0) {
            disp_index=i;
            break;
        }
    }
    if(disp_index<0) return; // no dispatcher found (unlikely)

    // After the last 'je block_x', insert call fake_func
    // The dispatcher consists of cmp rbx,x / je block_x lines.
    // so we'll find the last je block_x line:
    int insert_pos = disp_index+1;
    // AND scan forward until we reach a line not starting with 'cmp rbx,' or 'je block_'
    for(;insert_pos<P->count;insert_pos++){
        char *t=P->ins[insert_pos].text;
        if(strncmp(t,"cmp rbx,",8)!=0 && strncmp(t,"je block_",9)!=0){
            // not a cmp or je line, stop here
            break;
        }
    }

    // insert 'call fake_func' at insert_pos:
    Instruction ins;
    ins.label=NULL;
    char buf[256];sprintf(buf,"call %s", fake_func_label);
    ins.text=strdup(buf);
    ins.is_instruction=1;ins.is_directive=0;

    P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
    memmove(&P->ins[insert_pos+1],&P->ins[insert_pos],sizeof(Instruction)*(P->count - insert_pos));
    P->ins[insert_pos]=ins;
    P->count++;
}

// SECTOR 12 : Metamorphic Transformations
static void metamorphic_transform_instructions(Program *P) {
    // Register renaming map:
    // We'll pick a random renaming: rax->rcx, rbx->rdx, etc.
    // Just a fixed map for now, yk demonstration purposes and all:
    const char *regs[][2]={{"rax","rcx"},{"rbx","rsi"},{"rcx","r8"},{"rdx","r9"}};
    int reg_map_count=4;

    // Helper to rename registers in a line:
    auto rename_regs = [&](char *line) {
        for (int i=0;i<reg_map_count;i++){
            char *rfrom=(char*)regs[i][0];
            char *rto=(char*)regs[i][1];
            // Replace all occurrences of rfrom with rto:
            // ts is kind of a naive approach
            char buf[1024];buf[0]='\0';
            char *start=line;char *pos;
            while((pos=strstr(start,rfrom))){
                // ensure it's a standalone register name (check next char)
                int before_is_sep=(pos==line)||( !isalnum((unsigned char)pos[-1]) && pos[-1]!='_');
                int after_is_sep=(!isalnum((unsigned char)pos[strlen(rfrom)]) && pos[strlen(rfrom)]!='_');
                if(before_is_sep && after_is_sep) {
                    // replace
                    strncat(buf,start,(pos-start));
                    strcat(buf,rto);
                    start=pos+strlen(rfrom);
                } else {
                    // no replace
                    strncat(buf,start,(pos-start+strlen(rfrom)));
                    start=pos+strlen(rfrom);
                }
            }
            strcat(buf,start);
            strcpy(line,buf);
        }
    };

    for (int i=0;i<P->count;i++){
        if(!P->ins[i].is_instruction) continue;
        // rename registers:
        rename_regs(P->ins[i].text);

        // expand add rax,imm:
        if(strncmp(P->ins[i].text,"add rax,",8)==0) {
            char *imm_str=P->ins[i].text+8;
            while(*imm_str && isspace((unsigned char)*imm_str))imm_str++;
            uint64_t val=strtoull(imm_str,NULL,0);
            if(val>1 && val<10) {
                // expand
                // replace current instr with val times "inc rax"
                Instruction *new_list= (Instruction*)malloc(sizeof(Instruction)*(P->count+val-1));
                memcpy(new_list,P->ins,sizeof(Instruction)*i);
                for (uint64_t v=0;v<val;v++){
                    char buf[32];sprintf(buf,"inc rax");
                    new_list[i+v].label=NULL;
                    new_list[i+v].text=strdup(buf);
                    new_list[i+v].is_instruction=1;new_list[i+v].is_directive=0;
                }
                memcpy(&new_list[i+val], &P->ins[i+1], sizeof(Instruction)*(P->count-(i+1)));
                // free old line
                free(P->ins[i].text); if(P->ins[i].label)free(P->ins[i].label);
                free(P->ins);
                P->ins=new_list;
                P->count=P->count+(int)val-1;
                // adjust i so we don't skip instructions
                i+=(int)val-1;
            }
        }
    }
}


// SECTOR 13 : Insert Junk
static void insert_junk(Program *P) {
    const char* junk_ops[]={
        "xor rdx,rdx",
        "inc rdx",
        "dec rdx",
        "push rax\npop rax",
        "add rbx,0",
        "nop",
        "xchg rax,rax",
        "sub rsi,rsi",
        "mov r10, r10",
        "lea r11,[r11]"
    };
    int jcount = (int)(sizeof(junk_ops)/sizeof(junk_ops[0]));

    for(int i=0;i<P->count;i++){
        if(P->ins[i].is_instruction && (rand()%4==0)) {
            Instruction J;
            J.label=NULL;
            J.text=strdup(junk_ops[rand()%jcount]);
            J.is_instruction=1;
            J.is_directive=0;
            P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
            memmove(&P->ins[i+2],&P->ins[i+1],sizeof(Instruction)*(P->count-(i+1)));
            P->ins[i+1]=J;
            P->count++;
            i++;
        }
    }
}

// SECTOR 14 : Rename Labels
static void rename_labels(Program *P) {
    // Collect all labels and assign new names
    typedef struct {
        char *old;
        char *new_;
    } LabelRename;
    LabelRename *renames=NULL;int rcount=0,rcap=0;

    // gather labels
    for(int i=0;i<P->count;i++){
        if(P->ins[i].label) {
            if(rcount>=rcap){rcap=rcap?rcap*2:64;renames=realloc(renames,sizeof(LabelRename)*rcap);}
            renames[rcount].old=strdup(P->ins[i].label);
            renames[rcount].new_=random_label_name();
            // assign new label
            free(P->ins[i].label);
            P->ins[i].label=strdup(renames[rcount].new_);
            rcount++;
        }
    }

    // For each instruction that references these old labels, replace:
    // We'll look for patterns like "je old_label", "jmp old_label", etc.
    auto replace_label_refs = [&](char *line) {
        // okay going with a very simplistic approach: for each rename, search line for that old name as a standalone token.
        for (int r=0;r<rcount;r++){
            char *old=renames[r].old;
            char *new_=renames[r].new_;
            char buf[2048];buf[0]='\0';
            char *start=line;char *pos;
            while((pos=strstr(start,old))){
                // check word boundaries:
                int before_is_sep=(pos==line)||( !isalnum((unsigned char)pos[-1]) && pos[-1]!='_');
                int after_is_sep=(!isalnum((unsigned char)pos[strlen(old)]) && pos[strlen(old)]!='_');
                if(before_is_sep && after_is_sep) {
                    strncat(buf,start,pos-start);
                    strcat(buf,new_);
                    start=pos+strlen(old);
                } else {
                    strncat(buf,start,pos-start+strlen(old));
                    start=pos+strlen(old);
                }
            }
            strcat(buf,start);
            strcpy(line,buf);
        }
    };

    // replace references in instructions:
    for(int i=0;i<P->count;i++){
        if(P->ins[i].is_instruction){
            replace_label_refs(P->ins[i].text);
        }
    }

    for(int r=0;r<rcount;r++){
        free(renames[r].old);
        free(renames[r].new_);
    }
    free(renames);
}

// SECTOR 15 : Write Output
static void write_output(const char *filename, Program *P) {
    FILE *f=fopen(filename,"w");
    if(!f){perror("fopen output");exit(1);}
    for(int i=0;i<P->count;i++){
        if(P->ins[i].label) fprintf(f,"%s:\n",P->ins[i].label);
        if(strlen(P->ins[i].text)>0)
            fprintf(f,"%s\n",P->ins[i].text);
    }
    fclose(f);
}

// SECTOR fin : Main
int main(int argc,char**argv) {
    if(argc<3){
        fprintf(stderr,"Usage: %s input.s output.s\n",argv[0]);
        return 1;
    }
    srand(time(NULL));
    struct timespec start,end;
    clock_gettime(CLOCK_MONOTONIC,&start);

    Program P;memset(&P,0,sizeof(P));
    P.ins=read_instructions(argv[1],&P.count);

    extract_data(&P);
    encrypt_data(&P);

    fprintf(stderr,"[+] Building CFG...\n");
    P.cfg=build_cfg(P.ins,P.count);

    fprintf(stderr,"[+] Encrypting constants...\n");
    encrypt_constants(&P);

    fprintf(stderr,"[+] Inserting runtime decrypt stub (for constants)...\n");
    insert_runtime_decrypt_stub(&P);

    fprintf(stderr,"[+] Insert data decoder...\n");
    insert_data_decoder(&P);

    fprintf(stderr,"[+] Metamorphic transformations...\n");
    metamorphic_transform_instructions(&P);

    fprintf(stderr,"[+] Flattening CFG...\n");
    flatten_cfg(&P);

    fprintf(stderr,"[+] Inter-procedural obfuscation...\n");
    inter_procedural_obfuscation(&P);

    fprintf(stderr,"[+] Insert junk...\n");
    insert_junk(&P);

    fprintf(stderr,"[+] Rename labels...\n");
    rename_labels(&P);

    fprintf(stderr,"[+] Writing output...\n");
    write_output(argv[2], &P);

    clock_gettime(CLOCK_MONOTONIC,&end);
    double elapsed=(end.tv_sec - start.tv_sec)+(end.tv_nsec - start.tv_nsec)*1e-9;
    fprintf(stderr,"[+] Done in %.3f seconds.\n",elapsed);

    return 0;
}

// I cam hear the birds chirping outside. It's 5:30 AM. I should sleep. I'm cooked. I'm done. I'm out. Good night.