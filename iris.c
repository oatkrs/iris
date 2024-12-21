#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>

/*
    IRIS - Metamorphic Transformer
    --------------------------------
    1) Reads an input NASM .asm file.
    2) Builds a CFG & flattens it.
    3) Inserts junk instructions only in the .text section (avoiding parser issues).
    4) Renames labels, metamorphoses instructions, replaces pseudo-instructions.
    5) Removes lines containing ';'.
    6) Writes output.asm that compiles error-free, runs the same ("Hello, IRIS!").

    USAGE:
       gcc -o iris iris.c -lcapstone -lkeystone (if needed, or just plain gcc if these libs not strictly used)
       ./iris sample.asm output.asm
       nasm -f elf64 output.asm -o out.o
       gcc -no-pie -nostartfiles out.o -o out
       ./out
       => prints "Hello, IRIS!"
*/

// -------------------------------------------------------------------
// Data Structures
// -------------------------------------------------------------------
typedef struct {
    char *label;         // e.g. "_start"
    char *text;          // e.g. "mov rax,1"
    int is_instruction;  // 1 if real instruction, else 0
    int is_directive;    // 1 if e.g. 'section .text'
} Instruction;

typedef struct {
    int start_index;
    int end_index;
    char *name;   // e.g. "block_0"
    int id;
    int *succ;    
    int succ_count;
} BasicBlock;

typedef struct {
    BasicBlock *blocks;
    int block_count;
} CFG;

typedef struct {
    Instruction *ins;
    int count;
    CFG cfg;
} Program;

// -------------------------------------------------------------------
// Utility + Random
// -------------------------------------------------------------------
static char *random_label_name() {
    static const char chars[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    int len=8;
    char *buf=malloc(len+5);
    buf[0]='_'; buf[1]='_';
    for(int i=0; i<len; i++){
        buf[i+2] = chars[rand() % (sizeof(chars)-1)];
    }
    buf[len+2] = '_';
    buf[len+3] = '_';
    buf[len+4] = '\0';
    return buf;
}

// -------------------------------------------------------------------
// Reading Input ASM
// -------------------------------------------------------------------
static Instruction *read_instructions(const char *filename, int *count) {
    FILE *f=fopen(filename,"r");
    if(!f){ perror("fopen"); exit(1); }
    Instruction *list=NULL;
    int cap=0, cnt=0;
    char line[1024];

    while(fgets(line,sizeof(line),f)){
        char *p=line;
        // skip leading spaces
        while(*p && isspace((unsigned char)*p)) p++;
        if(*p=='\0' || *p=='\n') continue;

        // trim trailing
        char *end = p+strlen(p)-1;
        while(end>p && isspace((unsigned char)*end)){ *end='\0'; end--; }

        if(cnt>=cap){
            cap=cap?cap*2:128;
            list=realloc(list,sizeof(Instruction)*cap);
        }
        list[cnt].label=NULL;
        list[cnt].text=strdup(p);
        list[cnt].is_instruction=0;
        list[cnt].is_directive=0;

        // if there's a colon -> label
        char *colon=strchr(list[cnt].text,':');
        if(colon){
            *colon='\0';
            list[cnt].label=strdup(list[cnt].text);
            char *rest=colon+1;
            while(*rest && isspace((unsigned char)*rest)) rest++;
            free(list[cnt].text);
            list[cnt].text=strdup(rest);
        }
        // check directive
        if(list[cnt].text[0]=='.'){
            list[cnt].is_directive=1;
        } else if(strlen(list[cnt].text)>0){
            list[cnt].is_instruction=1;
        }
        cnt++;
    }
    fclose(f);
    *count=cnt;
    return list;
}

// -------------------------------------------------------------------
// CFG Building
// -------------------------------------------------------------------
typedef struct {
    char *name; 
    int   index;
} LabelMap;

static int is_jump_instr(const char *txt){
    if(strncmp(txt,"jmp",3)==0) return 1;
    if(txt[0]=='j' && strlen(txt)>1) return 1;
    return 0;
}
static int is_block_end(const char *txt){
    if(is_jump_instr(txt)) return 1;
    if(strncmp(txt,"ret",3)==0)return 1;
    if(strncmp(txt,"syscall",7)==0)return 1;
    return 0;
}
static int find_label_index(LabelMap*lm, int c, const char *n){
    for(int i=0; i<c; i++){
        if(strcmp(lm[i].name,n)==0)return lm[i].index;
    }
    return -1;
}
static LabelMap *build_label_map(Instruction *ins, int count, int *lc){
    LabelMap *lm=NULL; 
    int lm_count=0, lm_cap=0;
    for(int i=0; i<count; i++){
        if(ins[i].label){
            if(lm_count>=lm_cap){
                lm_cap=lm_cap? lm_cap*2:64;
                lm=realloc(lm,sizeof(LabelMap)*lm_cap);
            }
            lm[lm_count].name = strdup(ins[i].label);
            lm[lm_count].index= i;
            lm_count++;
        }
    }
    *lc=lm_count;
    return lm;
}

static CFG build_cfg(Instruction *ins, int count){
    int label_count=0;
    LabelMap* lm=build_label_map(ins,count,&label_count);

    int *block_starts=NULL;
    int bs_count=0, bs_cap=0;
    for(int i=0; i<count; i++){
        if(i==0 || ins[i].label){
            if(bs_count>=bs_cap){
                bs_cap=bs_cap? bs_cap*2:16;
                block_starts=realloc(block_starts,sizeof(int)*bs_cap);
            }
            block_starts[bs_count++]=i;
        }
    }
    typedef struct {int start; int end;} BE;
    BE*blocks=NULL;
    int blk_count=0, blk_cap=0;
    for(int i=0; i<bs_count; i++){
        int start=block_starts[i];
        int end=(i+1<bs_count)? (block_starts[i+1]-1):(count-1);
        for(int k=start; k<=end; k++){
            if(is_block_end(ins[k].text)){ end=k; break; }
        }
        if(blk_count>=blk_cap){
            blk_cap=blk_cap? blk_cap*2:16;
            blocks=realloc(blocks,sizeof(BE)*blk_cap);
        }
        blocks[blk_count].start=start;
        blocks[blk_count].end=end;
        blk_count++;
    }

    BasicBlock*BB=calloc(blk_count,sizeof(BasicBlock));
    for(int i=0; i<blk_count; i++){
        BB[i].start_index=blocks[i].start;
        BB[i].end_index  =blocks[i].end;
        BB[i].id=i;
        if(ins[BB[i].start_index].label){
            BB[i].name=strdup(ins[BB[i].start_index].label);
        } else {
            char buf[64];
            sprintf(buf,"block_%d",i);
            BB[i].name=strdup(buf);
        }
        BB[i].succ=NULL;
        BB[i].succ_count=0;

        int last=BB[i].end_index;
        char *txt=ins[last].text;
        if(is_jump_instr(txt)){
            char *space=strchr(txt,' ');
            if(space){
                char *target=space+1;
                while(*target && isspace((unsigned char)*target)) target++;
                int li=find_label_index(lm,label_count,target);
                if(li>=0){
                    int targ_blk=-1;
                    for(int u=0; u<blk_count; u++){
                        if(li>=BB[u].start_index && li<=BB[u].end_index){
                            targ_blk=u;
                            break;
                        }
                    }
                    if(strncmp(txt,"jmp",3)==0){
                        BB[i].succ=malloc(sizeof(int));
                        BB[i].succ[0]=targ_blk;
                        BB[i].succ_count=1;
                    } else {
                        BB[i].succ=malloc(sizeof(int)*2);
                        BB[i].succ[0]=targ_blk;
                        BB[i].succ_count=1;
                        int fall=BB[i].end_index+1;
                        for(int w=0; w<blk_count; w++){
                            if(fall>=BB[w].start_index && fall<=BB[w].end_index && w!=targ_blk){
                                BB[i].succ[BB[i].succ_count++]=w;
                                break;
                            }
                        }
                    }
                }
            }
        } else if(!is_block_end(txt)){
            int fall=BB[i].end_index+1;
            for(int w=0; w<blk_count; w++){
                if(fall>=BB[w].start_index && fall<=BB[w].end_index){
                    BB[i].succ=malloc(sizeof(int));
                    BB[i].succ[0]=w;
                    BB[i].succ_count=1;
                    break;
                }
            }
        }
    }
    CFG cfg; 
    cfg.blocks=BB;
    cfg.block_count=blk_count;

    for(int i=0; i<label_count; i++){
        free(lm[i].name);
    }
    free(lm);
    free(block_starts);
    free(blocks);
    return cfg;
}

// flatten_cfg: one .text, one global _start, then dispatcher, then blocks
static void flatten_cfg(Program *P) {
    CFG *cfg=&P->cfg;
    Instruction *new_list=NULL;
    int new_count=0, new_cap=0;

    #define ADDI(LBL,TXT) do{\
        if(new_count>=new_cap){\
            new_cap=new_cap?new_cap*2:256;\
            new_list=realloc(new_list,sizeof(Instruction)*new_cap);\
        }\
        new_list[new_count].label=(LBL)?strdup(LBL):NULL;\
        new_list[new_count].text=strdup(TXT);\
        new_list[new_count].is_directive=(TXT[0]=='.');\
        new_list[new_count].is_instruction=(!new_list[new_count].is_directive && strlen(TXT)>0);\
        new_count++;\
    }while(0)

    ADDI(NULL,"section .text");
    ADDI(NULL,".global _start");
    ADDI("_start:","mov rbx,0\njmp dispatcher");

    ADDI("dispatcher:","");
    for(int i=0; i<cfg->block_count; i++){
        char tmp[64];
        sprintf(tmp,"cmp rbx,%d",i);
        ADDI(NULL,tmp);
        sprintf(tmp,"je block_%d",i);
        ADDI(NULL,tmp);
    }

    for(int i=0; i<cfg->block_count; i++){
        char blocklab[64];
        sprintf(blocklab,"block_%d:",i);
        ADDI(blocklab,"nop");
        for(int k=cfg->blocks[i].start_index; k<=cfg->blocks[i].end_index; k++){
            if(P->ins[k].label && strcmp(P->ins[k].label, blocklab)==0){
                if(strlen(P->ins[k].text)>0){
                    ADDI(NULL,P->ins[k].text);
                }
            } else {
                if(strlen(P->ins[k].text)>0){
                    ADDI(NULL,P->ins[k].text);
                }
            }
        }
        if(cfg->blocks[i].succ_count>0){
            int nx=cfg->blocks[i].succ[0];
            char b2[64]; 
            sprintf(b2,"mov rbx, %d",nx);
            ADDI(NULL,b2);
            ADDI(NULL,"jmp dispatcher");
        }
    }

    for(int i=0; i<P->count; i++){
        free(P->ins[i].text);
        if(P->ins[i].label) free(P->ins[i].label);
    }
    free(P->ins);

    P->ins=new_list;
    P->count=new_count;

    #undef ADDI
}

// -------------------------------------------------------------------
// Insert Junk (only in .text)
// -------------------------------------------------------------------
static int is_in_text_section=0; // track when we are in text vs data
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
        "mov r10,r10",
        "lea r11,[r11]"
    };
    int jcount=(int)(sizeof(junk_ops)/sizeof(junk_ops[0]));

    for(int i=0; i<P->count; i++){
        // Check if current line is a "section .text"
        // or "section .data" => update is_in_text_section
        if(P->ins[i].is_directive && strstr(P->ins[i].text,"section .text")){
            is_in_text_section=1;
        } else if(P->ins[i].is_directive && strstr(P->ins[i].text,"section .data")){
            is_in_text_section=0;
        }

        // Insert junk only if we are in .text and current line is an instruction
        if(is_in_text_section && P->ins[i].is_instruction){
            if(rand()%4==0){ 
                // Insert junk after this line
                Instruction J;
                J.label=NULL;
                J.text=strdup(junk_ops[rand()%jcount]);
                J.is_directive=0; 
                J.is_instruction=1;
                P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
                memmove(&P->ins[i+2], &P->ins[i+1], sizeof(Instruction)*(P->count-(i+1)));
                P->ins[i+1]=J;
                P->count++;
                i++;
            }
        }
    }
}

// -------------------------------------------------------------------
// Metamorphic Transformations
// -------------------------------------------------------------------
static void rename_regs_in_line(char *line, const char *regs[][2], int n){
    for(int i=0; i<n; i++){
        const char *rfrom=regs[i][0];
        const char *rto=regs[i][1];
        char buff[1024]; 
        buff[0]='\0';
        const char *start=line;
        const char *pos;
        while((pos=strstr(start,rfrom))){
            int before_ok=(pos==start) || (!isalnum((unsigned char)pos[-1]) && pos[-1]!='_');
            const char *after=pos+strlen(rfrom);
            int after_ok=(!isalnum((unsigned char)*after) && *after!='_');
            if(before_ok && after_ok){
                strncat(buff,start,pos-start);
                strcat(buff,rto);
                start=pos+strlen(rfrom);
            } else {
                strncat(buff,start,(pos-start)+strlen(rfrom));
                start=pos+strlen(rfrom);
            }
        }
        strcat(buff,start);
        strcpy(line,buff);
    }
}

static void metamorphic_transform_instructions(Program *P){
    const char *regs[][2]={
        {"rax","rcx"},
        {"rbx","rsi"},
        {"rcx","r8"},
        {"rdx","r9"}
    };
    int n=4;

    for(int i=0; i<P->count; i++){
        if(!P->ins[i].is_instruction) continue;
        rename_regs_in_line(P->ins[i].text, regs, n);

        // expand "add rax, imm"
        if(strncmp(P->ins[i].text,"add rax,",8)==0){
            char *imm_str=P->ins[i].text+8;
            while(*imm_str && isspace((unsigned char)*imm_str)) imm_str++;
            uint64_t val=strtoull(imm_str,NULL,0);
            if(val>1 && val<10){
                P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+(val-1)));
                memmove(&P->ins[i+val], &P->ins[i+1], sizeof(Instruction)*(P->count-(i+1)));
                for(uint64_t v=0; v<val; v++){
                    P->ins[i+v].label=NULL;
                    P->ins[i+v].text=strdup("inc rax");
                    P->ins[i+v].is_instruction=1;
                    P->ins[i+v].is_directive=0;
                }
                free(P->ins[i].text);
                P->ins[i].text=NULL;
                P->count+=(val-1);
                i+=(val-1);
            }
        }
    }
}

// -------------------------------------------------------------------
// Label Renaming
// -------------------------------------------------------------------
static void replace_label_refs_in_line(char *line, char **old_labels, char **new_labels, int count){
    for(int r=0; r<count; r++){
        const char *old=old_labels[r];
        const char *new_=new_labels[r];
        char buff[2048];
        buff[0]='\0';
        const char *start=line;
        const char *pos;
        while((pos=strstr(start,old))){
            int before_ok=(pos==start)||(!isalnum((unsigned char)pos[-1]) && pos[-1]!='_');
            const char *after=pos+strlen(old);
            int after_ok=(!isalnum((unsigned char)*after) && *after!='_');
            if(before_ok && after_ok){
                strncat(buff,start,pos-start);
                strcat(buff,new_);
                start=pos+strlen(old);
            } else {
                strncat(buff,start,(pos-start)+strlen(old));
                start=pos+strlen(old);
            }
        }
        strcat(buff,start);
        strcpy(line,buff);
    }
}

static void rename_labels(Program *P){
    typedef struct {
        char *old; 
        char *new_;
    } LR;
    LR *arr=NULL; 
    int n=0,cap=0;

    for(int i=0; i<P->count; i++){
        if(P->ins[i].label){
            if(n>=cap){
                cap=cap?cap*2:64;
                arr=realloc(arr,sizeof(LR)*cap);
            }
            arr[n].old=strdup(P->ins[i].label);
            arr[n].new_=random_label_name();
            free(P->ins[i].label);
            P->ins[i].label=strdup(arr[n].new_);
            n++;
        }
    }
    if(n==0) return;
    char **old_labels=malloc(n*sizeof(char*));
    char **new_labels=malloc(n*sizeof(char*));
    for(int i=0; i<n; i++){
        old_labels[i]=arr[i].old;
        new_labels[i]=arr[i].new_;
    }
    // replace references
    for(int i=0; i<P->count; i++){
        if(P->ins[i].is_instruction){
            replace_label_refs_in_line(P->ins[i].text, old_labels, new_labels, n);
        }
    }
    for(int i=0; i<n; i++){
        free(arr[i].old);
        free(arr[i].new_);
    }
    free(arr);
    free(old_labels);
    free(new_labels);
}

// -------------------------------------------------------------------
// Replace Pseudo-Instructions
// -------------------------------------------------------------------
static void replace_pseudo_instructions(Program *P){
    // E.g. "write(1, msg, len)" => actual instructions
    // Also "exit(0)" => "mov rax,60 ; xor rdi,rdi ; syscall"
    typedef struct{
        const char *pseudo;
        const char *rep;
    } PP;

    PP arr[]={
        {
            "write(1, msg, len)",
            "mov rax,1\nmov rdi,1\nlea rsi,[rel msg]\nmov rdx,len\nsyscall"
        },
        {
            "exit(0)",
            "mov rax,60\nxor rdi,rdi\nsyscall"
        }
    };
    int rp_count=(int)(sizeof(arr)/sizeof(PP));

    for(int i=0; i<P->count; i++){
        if(!P->ins[i].is_instruction) continue;
        for(int j=0; j<rp_count; j++){
            if(strcmp(P->ins[i].text, arr[j].pseudo)==0){
                // expand
                char *mbuf=strdup(arr[j].rep);
                free(P->ins[i].text);

                char *saveptr=NULL;
                char *line=strtok_r(mbuf,"\n",&saveptr);
                if(line){
                    P->ins[i].text=strdup(line);
                    while((line=strtok_r(NULL,"\n",&saveptr))){
                        Instruction NI;
                        NI.label=NULL;
                        NI.text=strdup(line);
                        NI.is_directive=(line[0]=='.');
                        NI.is_instruction=(!NI.is_directive && strlen(line)>0);
                        P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
                        memmove(&P->ins[i+2],&P->ins[i+1],sizeof(Instruction)*(P->count-(i+1)));
                        P->ins[i+1]=NI;
                        P->count++;
                        i++;
                    }
                }
                free(mbuf);
            }
        }
    }
}

// -------------------------------------------------------------------
// Inter-Procedural Obfuscation
// -------------------------------------------------------------------
static void inter_procedural_obfuscation(Program *P){
    // Insert a 'fake function' 
    char *fk = random_label_name();
    Instruction newi;
    newi.label=strdup(fk);
    newi.text=strdup("xor rcx,rcx\nadd rcx,0x1337\ninc rcx\nret");
    newi.is_directive=0;
    newi.is_instruction=1;

    P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
    P->ins[P->count]=newi;
    P->count++;

    // Insert call in 'dispatcher:'
    int disp=-1;
    for(int i=0; i<P->count; i++){
        if(P->ins[i].label && strcmp(P->ins[i].label,"dispatcher:")==0){
            disp=i;
            break;
        }
    }
    if(disp<0) return;

    // Insert after the je lines
    int idx=disp+1;
    for(; idx<P->count; idx++){
        char *t=P->ins[idx].text;
        if(strncmp(t,"cmp rbx,",8)!=0 && strncmp(t,"je block_",9)!=0){
            break;
        }
    }
    // Insert "call fk"
    Instruction calli;
    calli.label=NULL;
    {
        char temp[128];
        sprintf(temp,"call %s", fk);
        calli.text=strdup(temp);
    }
    calli.is_directive=0;
    calli.is_instruction=1;
    P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
    memmove(&P->ins[idx+1],&P->ins[idx],sizeof(Instruction)*(P->count-idx));
    P->ins[idx]=calli;
    P->count++;
}

// -------------------------------------------------------------------
// Remove Lines Containing ';'
// -------------------------------------------------------------------
static void strip_comment_lines(Program *P){
    for(int i=0; i<P->count; i++){
        char *sc=strchr(P->ins[i].text,';');
        if(sc){
            // remove from sc onward
            *sc='\0';
            // trim trailing
            char *end=P->ins[i].text+strlen(P->ins[i].text)-1;
            while(end>=P->ins[i].text && isspace((unsigned char)*end)){
                *end='\0';
                end--;
            }
        }
    }
}

// -------------------------------------------------------------------
// Write Output
// -------------------------------------------------------------------
static void write_output(const char *filename, Program *P){
    FILE *f=fopen(filename,"w");
    if(!f){
        perror("fopen output");
        exit(1);
    }
    for(int i=0; i<P->count; i++){
        // print label with colon
        if(P->ins[i].label){
            if(strlen(P->ins[i].label)>0 && P->ins[i].label[strlen(P->ins[i].label)-1] != ':'){
                fprintf(f,"%s:\n",P->ins[i].label);
            } else {
                fprintf(f,"%s\n",P->ins[i].label);
            }
        }
        // print line if there's text
        if(strlen(P->ins[i].text)>0){
            fprintf(f,"%s\n",P->ins[i].text);
        }
    }
    fclose(f);
}

// -------------------------------------------------------------------
// main
// -------------------------------------------------------------------
int main(int argc, char**argv){
    if(argc<3){
        fprintf(stderr,"Usage: %s input.asm output.asm\n",argv[0]);
        return 1;
    }
    srand(time(NULL));

    Program P; 
    memset(&P,0,sizeof(P));

    // read
    P.ins=read_instructions(argv[1], &P.count);

    // build CFG
    P.cfg=build_cfg(P.ins,P.count);

    // metamorph
    metamorphic_transform_instructions(&P);

    // flatten
    flatten_cfg(&P);

    // inter-proc
    inter_procedural_obfuscation(&P);

    // insert junk only in .text
    insert_junk(&P);

    // rename labels
    rename_labels(&P);

    // replace pseudo
    replace_pseudo_instructions(&P);

    // remove lines with ';'
    strip_comment_lines(&P);

    // write
    write_output(argv[2], &P);

    fprintf(stderr,"[+] Done. Next steps:\n"
                   "    nasm -f elf64 %s -o out.o\n"
                   "    gcc -no-pie -nostartfiles out.o -o out\n"
                   "    ./out\n",argv[2]);
    return 0;
}
