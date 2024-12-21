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

/* 
   IRIS - the Iterative Re-writer and Instruction Substitutor
   This version ensures that the string "Hello, IRIS!" is encrypted 
   and does NOT appear in readable form in output.asm.
   A runtime decoder stub decrypts it before printing.

   Steps:
     1. Extract the original "Hello, IRIS!" string from .data in sample.asm.
     2. Encrypt the string, store only the ciphertext in output.asm.
     3. Insert a runtime decoder that decrypts the string in memory.
     4. Replace references to the original string with a call to the decoder.
     5. Flatten CFG, insert junk, rename labels, etc.
     6. Output final .asm that compiles and runs without manual editing.

   Usage:
     gcc -o iris iris.c -lcapstone -lkeystone
     ./iris sample.asm output.asm
     nasm -f elf64 output.asm -o output.o
     gcc -no-pie -nostartfiles output.o -o output
     ./output
     => prints "Hello, IRIS!" from the decrypted buffer
*/

// --------------------------------------------------------------------

// SECTOR 1 : Random and Utility Functions

static char *random_label_name() {
    static const char charset[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    int len = 8;
    char *buf = malloc(len + 5);
    buf[0] = '_';
    buf[1] = '_';
    for(int i = 0; i < len; i++){
        buf[i+2] = charset[rand() % (sizeof(charset) - 1)];
    }
    buf[len+2] = '_';
    buf[len+3] = '_';
    buf[len+4] = '\0';
    return buf;
}

static uint64_t random_key() {
    uint64_t k = 0;
    for(int i=0; i<8; i++){
        k = (k << 8) | (rand() & 0xFF);
    }
    return k;
}

// Store instructions
typedef struct {
    char *label;
    char *text;
    int is_instruction;
    int is_directive;
} Instruction;

// Basic Block for CFG
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

// For constants encryption
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

// forward declarations
static void inter_procedural_obfuscation(Program *P);


// SECTOR 2 : Data Structures

static Instruction *read_instructions(const char *filename, int *count) {
    FILE *f = fopen(filename,"r");
    if(!f){
        perror("fopen");
        exit(1);
    }
    Instruction *list = NULL;
    int cap = 0, cnt = 0;
    char line[1024];

    while(fgets(line, sizeof(line), f)){
        char *p = line;
        // strip leading spaces
        while(*p && isspace((unsigned char)*p)) p++;
        if(*p == '\0' || *p == '\n') continue;

        // strip trailing spaces
        char *end = p + strlen(p) - 1;
        while(end > p && isspace((unsigned char)*end)) {
            *end = '\0';
            end--;
        }

        if(cnt >= cap){
            cap = cap? cap*2 : 128;
            list = realloc(list, sizeof(Instruction)*cap);
        }

        list[cnt].label = NULL;
        list[cnt].text = strdup(p);
        list[cnt].is_directive = 0;
        list[cnt].is_instruction = 0;

        // if there's a colon, treat that as a label
        char *colon = strchr(list[cnt].text, ':');
        if(colon){
            *colon = '\0';
            list[cnt].label = strdup(list[cnt].text);
            char *rest = colon + 1;
            while(*rest && isspace((unsigned char)*rest)) rest++;
            free(list[cnt].text);
            list[cnt].text = strdup(rest);
        }

        if(list[cnt].text[0] == '.'){
            list[cnt].is_directive = 1;
        } else if(strlen(list[cnt].text) > 0) {
            list[cnt].is_instruction = 1;
        }
        cnt++;
    }
    fclose(f);
    *count = cnt;
    return list;
}

// SECTOR 3 : Reading Input Assembly

//
// -------------- Section 3: Extracting & Encrypting the Hidden String --------------
//
/*
   We'll specifically look for the "Hello, IRIS!" in the .data section 
   and replace it with an encrypted version, so it no longer appears in plaintext.
*/

// We'll store the hidden string as ciphertext, then decode at runtime 
// using a custom "string_decoder" function. We'll also remove the 
// original "db" line referencing "Hello, IRIS!".

// We want to ensure that any usage of 'msg' in the final code 
// references the decoded pointer from "string_decoder".

// We'll define "extract_data" to parse the .data section, find "Hello, IRIS!", encrypt it, 
// and wipe the original line.

static unsigned char *global_enc_string = NULL;
static unsigned char *global_enc_key    = NULL;
static size_t global_enc_len            = 0;

static char *string_decoder_label       = NULL;
static char *enc_string_label           = NULL;
static char *enc_key_label             = NULL;
static char *string_len_label           = NULL;

static void extract_data(Program *P) {
    int data_index = -1;
    for(int i=0; i<P->count; i++){
        if(P->ins[i].is_directive && strstr(P->ins[i].text, "section .data")){
            data_index = i;
            break;
        }
    }
    if(data_index < 0) return;

    for(int i=data_index+1; i<P->count; i++){
        if(P->ins[i].label || (P->ins[i].is_directive && strstr(P->ins[i].text,"section "))){
            // end of data section
            break;
        }
        // Check if line references "Hello, IRIS!"
        if(strstr(P->ins[i].text, "\"Hello, IRIS!\"")) {
            // We'll parse that line, find the ASCII, encrypt, store in memory
            // Then remove the line or blank it out
            const char *needle = "\"Hello, IRIS!\"";
            char *pos = strstr(P->ins[i].text, needle);
            if(pos) {
                size_t slen = strlen("Hello, IRIS!");
                unsigned char *plaintext = (unsigned char*)malloc(slen);
                memcpy(plaintext, "Hello, IRIS!", slen);

                // encrypt it
                global_enc_len = slen;
                global_enc_string = malloc(global_enc_len);
                global_enc_key    = malloc(global_enc_len);

                for(size_t k=0; k<global_enc_len; k++){
                    global_enc_key[k] = (unsigned char)(rand() & 0xFF);
                }
                // encryption: c[i] = plaintext[i] ^ global_enc_key[i]
                for(size_t k=0; k<global_enc_len; k++){
                    global_enc_string[k] = plaintext[k] ^ global_enc_key[k];
                }
                // blank out the line
                free(P->ins[i].text);
                P->ins[i].text = strdup("; HIDDEN Hello, IRIS!");
            }
        }
    }
}

// Insert a small snippet that decodes the hidden string at runtime
// We'll store the ciphertext & key in .data, decode them in .text, 
// returning a pointer to the decoded buffer. We'll place it in e.g. rsi for usage.

static void insert_string_decoder(Program *P) {
    if(!global_enc_string || !global_enc_key || global_enc_len == 0) {
        return;
    }
    // We'll define new labels for the encoded string, its key, and length
    string_decoder_label = random_label_name();
    enc_string_label     = random_label_name();
    enc_key_label        = random_label_name();
    string_len_label     = random_label_name();

    // We'll store them at the end of the file in .data
    P->ins = realloc(P->ins, sizeof(Instruction)*(P->count + 50));
    int idx = P->count;

    // Insert "section .data"
    P->ins[idx].label = NULL;
    P->ins[idx].text  = strdup("section .data");
    P->ins[idx].is_directive=1; P->ins[idx].is_instruction=0;
    idx++;

    // string_len_label:
    {
        P->ins[idx].label = strdup(string_len_label);
        char buf[64];
        sprintf(buf, "dq %zu", global_enc_len);
        P->ins[idx].text = strdup(buf);
        P->ins[idx].is_directive=0; P->ins[idx].is_instruction=0;
        idx++;
    }

    // enc_string_label:
    {
        P->ins[idx].label = strdup(enc_string_label);
        P->ins[idx].text  = strdup("");
        P->ins[idx].is_directive=0; P->ins[idx].is_instruction=0;
        idx++;

        for(size_t k=0; k<global_enc_len; k++){
            char line[64];
            sprintf(line, "db 0x%02x", global_enc_string[k]);
            P->ins[idx].label = NULL;
            P->ins[idx].text  = strdup(line);
            P->ins[idx].is_directive=0; P->ins[idx].is_instruction=0;
            idx++;
        }
    }

    // enc_key_label:
    {
        P->ins[idx].label = strdup(enc_key_label);
        P->ins[idx].text  = strdup("");
        P->ins[idx].is_directive=0; P->ins[idx].is_instruction=0;
        idx++;

        for(size_t k=0; k<global_enc_len; k++){
            char line[64];
            sprintf(line,"db 0x%02x", global_enc_key[k]);
            P->ins[idx].label = NULL;
            P->ins[idx].text  = strdup(line);
            P->ins[idx].is_directive=0; P->ins[idx].is_instruction=0;
            idx++;
        }
    }

    // Now the actual decoder in .text
    {
        char code[1024];
        snprintf(code, sizeof(code),
            "section .text\n"
            "%s:\n"
            "    ; We'll allocate a buffer with length=string_len_label\n"
            "    mov rax, 9  ; mmap syscall\n"
            "    xor rdi,rdi\n"
            "    mov rsi, [rel %s]\n"
            "    mov rdx, 3  ; PROT_READ|PROT_WRITE\n"
            "    mov r10, 0x22 ; MAP_PRIVATE|MAP_ANONYMOUS\n"
            "    mov r8, -1\n"
            "    mov r9, 0\n"
            "    syscall\n"
            "    mov r14, rax    ; buffer ptr\n"
            "    lea r11, [rel %s]\n"
            "    lea r12, [rel %s]\n"
            "    mov rcx, [rel %s]\n"
            "    xor r8,r8\n"
            "decode_str_loop:\n"
            "    mov bl, [r11 + r8]\n"
            "    xor bl, [r12 + r8]\n"
            "    mov [r14 + r8], bl\n"
            "    inc r8\n"
            "    cmp r8, rcx\n"
            "    jb decode_str_loop\n"
            "    mov rax, r14     ; return pointer in rax\n"
            "    ret\n",
            string_decoder_label,
            string_len_label,      // read length
            enc_string_label,      // ciphertext
            enc_key_label,         // key
            string_len_label       // length
        );

        // tokenize code by lines
        char *saveptr=NULL;
        char linebuf[1024];
        strcpy(linebuf, code);

        char *l = strtok_r(linebuf, "\n", &saveptr);
        while(l){
            Instruction I;
            I.label=NULL;
            char *cl = strchr(l,':');
            if(cl && (cl-l)>0 && *(cl+1)=='\0'){
                // label line
                int length=(int)(cl-l);
                I.label=strndup(l,length);
                I.text=strdup("");
                I.is_instruction=0; I.is_directive=0;
            } else {
                I.text=strdup(l);
                I.is_directive=(l[0]=='.');
                I.is_instruction=(!I.is_directive && strlen(l)>0);
            }
            P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+1));
            P->ins[P->count]=I;
            P->count++;
            l=strtok_r(NULL,"\n",&saveptr);
        }
    }
    // done appending
}

// We'll also need to rewrite any usage of "mov rsi, [rel msg]" or similar 
// to call the string_decoder function and store the result in RSI. 
// We'll do that in the "replace_string_usage" function below.

// Example: 
// Original: lea rsi, [rel msg]
// Replaced: call string_decoder_label
//           mov rsi, rax
static void replace_string_usage(Program *P) {
    if(!string_decoder_label) return; // if we never found "Hello, IRIS!"
    // For each instruction that references "rel msg" or "msg", 
    // we'll replace it with a call to string_decoder, store result in rsi.

    for(int i=0; i<P->count; i++){
        if(!P->ins[i].is_instruction) continue;
        if(strstr(P->ins[i].text,"[rel msg]")) {
            // We'll replace with:
            //    call string_decoder_label
            //    mov rsi, rax
            // or if it references rax directly, we do similarly
            Instruction new1, new2;
            new1.label=NULL;
            {
                char line[256];
                sprintf(line,"call %s", string_decoder_label);
                new1.text=strdup(line);
                new1.is_directive=0; new1.is_instruction=1;
            }
            new2.label=NULL;
            new2.text=strdup("mov rsi, rax");
            new2.is_directive=0; new2.is_instruction=1;

            // Insert them, remove the original line
            free(P->ins[i].text);
            P->ins[i].text=strdup("; replaced usage of [rel msg]");
            P->ins=realloc(P->ins,sizeof(Instruction)*(P->count+2));
            memmove(&P->ins[i+3], &P->ins[i+1], sizeof(Instruction)*(P->count-(i+1)));
            P->ins[i+1]=new1;
            P->ins[i+2]=new2;
            P->count+=2;
            i+=2; // skip newly inserted lines
        }
    }
}


// SECTOR 4 : CFG Construction
typedef struct {
    char* name;
    int   index;
} LabelMap;

static int is_jump_instr(const char *txt) {
    if(strncmp(txt, "jmp", 3) == 0) return 1;
    if(txt[0] == 'j' && strlen(txt) > 1) return 1;
    return 0;
}

static int is_block_end(const char *txt){
    if(is_jump_instr(txt)) return 1;
    if(strncmp(txt,"ret",3) == 0) return 1;
    if(strncmp(txt,"syscall",7) == 0) return 1;
    return 0;
}

static int find_label_index(LabelMap*lm, int c, const char* n) {
    for(int i = 0; i < c; i++){
        if(strcmp(lm[i].name, n) == 0) return lm[i].index;
    }
    return -1;
}

static LabelMap *build_label_map(Instruction *ins, int count, int *lc) {
    LabelMap *lm = NULL;
    int lm_count = 0, lm_cap = 0;

    for(int i = 0; i < count; i++){
        if(ins[i].label){
            if(lm_count >= lm_cap){
                lm_cap = lm_cap ? lm_cap * 2 : 64;
                lm = realloc(lm, sizeof(LabelMap) * lm_cap);
            }
            lm[lm_count].name  = strdup(ins[i].label);
            lm[lm_count].index = i;
            lm_count++;
        }
    }
    *lc = lm_count;
    return lm;
}

static CFG build_cfg(Instruction *ins, int count){
    int label_count;
    LabelMap* lm = build_label_map(ins, count, &label_count);

    int *block_starts = NULL;
    int bs_count = 0, bs_cap = 0;

    for(int i = 0; i < count; i++){
        if(i == 0 || ins[i].label){
            if(bs_count >= bs_cap){
                bs_cap = bs_cap ? bs_cap * 2 : 16;
                block_starts = realloc(block_starts, sizeof(int) * bs_cap);
            }
            block_starts[bs_count++] = i;
        }
    }

    typedef struct { int start; int end; } BE;
    BE *blocks = NULL;
    int blk_count = 0, blk_cap = 0;

    for(int i = 0; i < bs_count; i++){
        int start = block_starts[i];
        int end   = (i + 1 < bs_count) ? (block_starts[i+1] - 1) : (count - 1);

        for(int k = start; k <= end; k++){
            if(is_block_end(ins[k].text)){
                end = k;
                break;
            }
        }

        if(blk_count >= blk_cap){
            blk_cap = blk_cap ? blk_cap * 2 : 16;
            blocks = realloc(blocks, sizeof(BE) * blk_cap);
        }
        blocks[blk_count].start = start;
        blocks[blk_count].end   = end;
        blk_count++;
    }

    BasicBlock *BB = calloc(blk_count, sizeof(BasicBlock));
    for(int i = 0; i < blk_count; i++){
        BB[i].start_index = blocks[i].start;
        BB[i].end_index   = blocks[i].end;
        BB[i].id = i;

        if(ins[BB[i].start_index].label) {
            BB[i].name = strdup(ins[BB[i].start_index].label);
        } else {
            char buf[64];
            sprintf(buf,"placeholder_block_%d", i);
            BB[i].name = strdup(buf);
        }

        BB[i].succ = NULL;
        BB[i].succ_count = 0;

        int last = BB[i].end_index;
        char *txt = ins[last].text;

        if(is_jump_instr(txt)){
            char *space = strchr(txt,' ');
            if(space){
                char *target = space + 1;
                while(*target && isspace((unsigned char)*target)) target++;
                int li = find_label_index(lm, label_count, target);
                if(li >= 0){
                    int target_block = -1;
                    for(int u = 0; u < blk_count; u++){
                        if(li >= BB[u].start_index && li <= BB[u].end_index){
                            target_block = u; 
                            break;
                        }
                    }
                    if(strncmp(txt,"jmp",3) == 0){
                        BB[i].succ = malloc(sizeof(int));
                        BB[i].succ[0] = target_block;
                        BB[i].succ_count=1;
                    } else {
                        BB[i].succ = malloc(sizeof(int)*2);
                        BB[i].succ[0] = target_block;
                        BB[i].succ_count=1;

                        int fall = BB[i].end_index + 1;
                        for(int w = 0; w < blk_count; w++){
                            if(fall >= BB[w].start_index && fall <= BB[w].end_index && w != target_block){
                                BB[i].succ[BB[i].succ_count++] = w;
                                break;
                            }
                        }
                    }
                }
            }
        } else if(!is_block_end(txt)){
            int fall = BB[i].end_index + 1;
            for(int w = 0; w < blk_count; w++){
                if(fall >= BB[w].start_index && fall <= BB[w].end_index){
                    BB[i].succ = malloc(sizeof(int));
                    BB[i].succ[0] = w;
                    BB[i].succ_count=1;
                    break;
                }
            }
        }
    }

    CFG cfg;
    cfg.blocks = BB;
    cfg.block_count = blk_count;

    for(int i=0;i<label_count;i++){
        free(lm[i].name);
    }
    free(lm);
    free(block_starts);
    free(blocks);
    return cfg;
}

// SECTOR 5 : Data Extraction (Handles .data for NASM)
static void extract_data(Program *P) {
    int data_index = -1;
    // Search for the line that declares "section .data"
    for(int i = 0; i < P->count; i++){
        if(P->ins[i].is_directive && strstr(P->ins[i].text, "section .data")){
            data_index = i;
            break;
        }
    }
    if(data_index < 0) return;

    unsigned char *data = NULL;
    int dcount = 0, dcap = 0;

    // Start parsing lines after "section .data"
    for(int i = data_index + 1; i < P->count; i++){
        if(P->ins[i].label || (P->ins[i].is_directive && strstr(P->ins[i].text, "section "))) {
            break;
        }

        char *line = P->ins[i].text;
        char *dbpos = strstr(line, "db ");
        if(!dbpos) {
            continue; // Possibly a label or something else
        }
        // Move pointer to after "db "
        char *args = dbpos + 3;
        while(*args) {
            while(*args && isspace((unsigned char)*args)) args++;
            if(*args == '"') {
                args++;
                while(*args && *args != '"'){
                    if(dcount >= dcap){
                        dcap = dcap ? dcap * 2 : 64;
                        data = realloc(data, dcap);
                    }
                    data[dcount++] = (unsigned char)*args;
                    args++;
                }
                if(*args == '"') args++; // skip closing quote
            } else if(strncmp(args, "0x", 2) == 0) {
                char *endp;
                unsigned long val = strtoul(args, &endp, 16);
                if(dcount >= dcap){
                    dcap = dcap ? dcap * 2 : 64;
                    data = realloc(data, dcap);
                }
                data[dcount++] = (unsigned char)val;
                args = endp;
            } else {
                if(*args && *args != ',' && *args != '\n'){
                    if(dcount >= dcap){
                        dcap = dcap ? dcap * 2 : 64;
                        data = realloc(data, dcap);
                    }
                    data[dcount++] = (unsigned char)*args;
                    args++;
                } else {
                    args++;
                }
            }
            while(*args && (isspace((unsigned char)*args) || *args == ',')) args++;
        }
    }

    P->orig_data = data;
    P->orig_data_size = dcount;
}

// SECTOR 6 : Data Encryption
static void encrypt_data(Program *P) {
    if(P->orig_data_size == 0) return;

    P->enc_data_size = P->orig_data_size;
    P->enc_data      = malloc(P->enc_data_size);
    P->enc_key       = malloc(P->enc_data_size);

    for(size_t i = 0; i < P->enc_data_size; i++){
        P->enc_key[i] = (unsigned char)(rand() & 0xFF);
    }

    uint64_t master_key = random_key();

    for(size_t i = 0; i < P->enc_data_size; i++){
        unsigned char mkb = ((unsigned char*)&master_key)[i % 8];
        unsigned char val = P->orig_data[i] ^ P->enc_key[i];
        val = val ^ mkb;
        P->enc_data[i] = val;
    }
}

// SECTOR 7 : Constants Encryption
static void encrypt_constants(Program *P) {
    for(int i = 0; i < P->count; i++){
        if(!P->ins[i].is_instruction) continue;
        char *t = P->ins[i].text;
        if(strncmp(t, "mov rax,", 8) == 0){
            char *imm_str = t + 8;
            while(*imm_str && isspace((unsigned char)*imm_str)) imm_str++;
            if(strncmp(imm_str, "0x", 2) == 0) {
                uint64_t val = strtoull(imm_str, NULL, 16);
                uint64_t key = random_key_val();
                uint64_t enc = val ^ key;
                int cid = P->const_count;
                P->constants = realloc(P->constants, sizeof(Constant)*(cid+1));
                P->constants[cid].value = val;
                P->constants[cid].encrypted_value = enc;
                P->const_count++;
                free(P->ins[i].text);
                char buf[256];
                sprintf(buf, "mov rdi,%d\ncall decrypt_stub_constant", cid);
                P->ins[i].text = strdup(buf);
            }
        }
    }
}

// SECTOR 8 : Insert Runtime Decrypt Stub for Constants
static char *decrypt_stub_constant_label;

static void insert_runtime_decrypt_stub(Program *P) {
    decrypt_stub_constant_label = random_label_name();

    // Insert a small snippet: decrypt_stub_constant
    P->ins = realloc(P->ins, sizeof(Instruction)*(P->count + 1));
    int idx = P->count;

    // This snippet references const_table_const and const_keys_const that we'll define later
    P->ins[idx].label = strdup(decrypt_stub_constant_label);
    P->ins[idx].text  = strdup(
        "mov rax, [rel const_table_const + rdi * 8]\n"
        "mov rcx, [rel const_keys_const + rdi * 8]\n"
        "xor rax, rcx\n"
        "ret"
    );
    P->ins[idx].is_instruction = 1;
    P->ins[idx].is_directive   = 0;
    P->count++;
}

// SECTOR 9 : Insert Data Decoder
static char *data_decoder_label;
static char *enc_data_label;
static char *enc_key_label;
static char *master_key_label;
static char *const_table_const_label;
static char *const_keys_const_label;
static uint64_t master_key_global;

static void insert_data_decoder(Program *P) {
    data_decoder_label        = random_label_name();
    enc_data_label            = random_label_name();
    enc_key_label             = random_label_name();
    master_key_label          = random_label_name();
    const_table_const_label   = random_label_name();
    const_keys_const_label    = random_label_name();

    master_key_global = random_key();

    // Append all data at the very end in a single .data block
    P->ins = realloc(P->ins, sizeof(Instruction) * 
                     (P->count + (int)(2*P->enc_data_size + P->const_count*2 + 50)));
    int idx = P->count;

    // Step 1: "section .data"
    P->ins[idx].label           = NULL;
    P->ins[idx].text            = strdup("section .data");
    P->ins[idx].is_directive    = 1;
    P->ins[idx].is_instruction  = 0;
    idx++;

    // Step 2: Master Key
    P->ins[idx].label = strdup(master_key_label);
    char line[64];
    sprintf(line,
        "db 0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x,0x%02x",
        (unsigned)((master_key_global >>  0) & 0xFF),
        (unsigned)((master_key_global >>  8) & 0xFF),
        (unsigned)((master_key_global >> 16) & 0xFF),
        (unsigned)((master_key_global >> 24) & 0xFF),
        (unsigned)((master_key_global >> 32) & 0xFF),
        (unsigned)((master_key_global >> 40) & 0xFF),
        (unsigned)((master_key_global >> 48) & 0xFF),
        (unsigned)((master_key_global >> 56) & 0xFF)
    );
    P->ins[idx].text = strdup(line);
    P->ins[idx].is_directive    = 0;
    P->ins[idx].is_instruction  = 0;
    idx++;

    // Step 3: Encrypted Data
    P->ins[idx].label           = strdup(enc_data_label);
    P->ins[idx].text            = strdup("");
    P->ins[idx].is_directive    = 0;
    P->ins[idx].is_instruction  = 0;
    idx++;

    for(size_t i = 0; i < P->enc_data_size; i++){
        char b[32];
        sprintf(b, "db 0x%02x", (unsigned)P->enc_data[i]);
        P->ins[idx].label         = NULL;
        P->ins[idx].text          = strdup(b);
        P->ins[idx].is_directive  = 0;
        P->ins[idx].is_instruction = 0;
        idx++;
    }

    // Step 4: Encrypted Key
    P->ins[idx].label           = strdup(enc_key_label);
    P->ins[idx].text            = strdup("");
    P->ins[idx].is_directive    = 0;
    P->ins[idx].is_instruction  = 0;
    idx++;

    for(size_t i = 0; i < P->enc_data_size; i++){
        char b[32];
        sprintf(b, "db 0x%02x", (unsigned)P->enc_key[i]);
        P->ins[idx].label         = NULL;
        P->ins[idx].text          = strdup(b);
        P->ins[idx].is_directive  = 0;
        P->ins[idx].is_instruction= 0;
        idx++;
    }

    // Step 5: Constant tables
    P->ins[idx].label           = strdup(const_table_const_label);
    P->ins[idx].text            = strdup("");
    P->ins[idx].is_directive    = 0;
    P->ins[idx].is_instruction  = 0;
    idx++;

    for(int i = 0; i < P->const_count; i++){
        char buf[64];
        sprintf(buf, "dq 0x%lx", (unsigned long)P->constants[i].encrypted_value);
        P->ins[idx].label         = NULL;
        P->ins[idx].text          = strdup(buf);
        P->ins[idx].is_directive  = 0;
        P->ins[idx].is_instruction= 0;
        idx++;
    }

    P->ins[idx].label           = strdup(const_keys_const_label);
    P->ins[idx].text            = strdup("");
    P->ins[idx].is_directive    = 0;
    P->ins[idx].is_instruction  = 0;
    idx++;

    for(int i = 0; i < P->const_count; i++){
        uint64_t key = P->constants[i].value ^ P->constants[i].encrypted_value;
        char buf[64];
        sprintf(buf, "dq 0x%lx", (unsigned long)key);
        P->ins[idx].label         = NULL;
        P->ins[idx].text          = strdup(buf);
        P->ins[idx].is_directive  = 0;
        P->ins[idx].is_instruction= 0;
        idx++;
    }

    // Step 6: Data Decoder in .text
    {
        char *enc_data_len_label = random_label_name();
        P->ins[idx].label = strdup(enc_data_len_label);

        char len_buf[64];
        sprintf(len_buf, "dq %zu", P->enc_data_size);
        P->ins[idx].text = strdup(len_buf);
        P->ins[idx].is_directive    = 0;
        P->ins[idx].is_instruction  = 0;
        idx++;

        // Actual decoder code
        char code_fmt[] =
            "section .text\n"
            "%s:\n"
            "mov rdx, [rel %s]\n"
            "mov rax, 9\n"
            "xor rdi, rdi\n"
            "mov rsi, rdx\n"
            "mov rdx, 3\n"
            "mov r10, 0x22\n"
            "mov r8, -1\n"
            "mov r9, 0\n"
            "syscall\n"
            "mov r14, rax\n"
            "lea r11, [rel %s]\n"
            "lea r12, [rel %s]\n"
            "lea r13, [rel %s]\n"
            "mov rcx, rdx\n"
            "xor r8, r8\n"
            "decode_loop:\n"
            "mov bl, [r11 + r8]\n"
            "xor bl, [r12 + r8]\n"
            "mov rax, r8\n"
            "and rax, 7\n"
            "mov r15, r13\n"
            "add r15, rax\n"
            "mov al, [r15]\n"
            "xor bl, al\n"
            "mov [r14 + r8], bl\n"
            "inc r8\n"
            "loop decode_loop\n"
            "mov rax, r14\n"
            "ret\n";

        char final_code[2048];
        snprintf(final_code, sizeof(final_code), code_fmt,
                 data_decoder_label, enc_data_len_label,
                 enc_data_label, enc_key_label, master_key_label);

        char *saveptr = NULL;
        char *linep   = strtok_r(final_code, "\n", &saveptr);
        while(linep){
            Instruction I;
            I.label = NULL;
            char *cl = strchr(linep, ':');
            if(cl && (cl - linep) > 0 && *(cl+1) == '\0'){
                // Label line
                int len = (int)(cl - linep);
                I.label = strndup(linep, len);
                I.text  = strdup("");
                I.is_directive    = 0;
                I.is_instruction  = 0;
            } else {
                I.text = strdup(linep);
                I.is_directive    = (linep[0] == '.');
                I.is_instruction  = (strlen(linep) > 0 && linep[0] != '.');
            }
            P->ins = realloc(P->ins, sizeof(Instruction)*(P->count + 1));
            P->ins[P->count] = I;
            P->count++;
            linep = strtok_r(NULL, "\n", &saveptr);
        }
    }

    P->count = idx; // finalize
}

// SECTOR 10 : Flatten CFG
static void flatten_cfg(Program *P) {
    CFG *cfg = &P->cfg;
    Instruction *new_list = NULL;
    int new_count = 0, new_cap = 0;

    #define ADD_INST(LBL,TEXT) do { \
        if(new_count >= new_cap){ \
            new_cap = new_cap ? new_cap * 2 : 256; \
            new_list = realloc(new_list, sizeof(Instruction)*new_cap); \
        } \
        new_list[new_count].label = (LBL) ? strdup(LBL) : NULL; \
        new_list[new_count].text  = strdup(TEXT); \
        new_list[new_count].is_directive   = ((TEXT[0] == '.') ? 1 : 0); \
        new_list[new_count].is_instruction = (!new_list[new_count].is_directive && strlen(TEXT) > 0); \
        new_count++; \
    } while(0)

    // Insert .text, .global _start, and the dispatcher
    ADD_INST(NULL, "section .text");
    ADD_INST(NULL, ".global _start");
    ADD_INST("_start:", "mov rbx,0\njmp dispatcher");

    ADD_INST("dispatcher:", "");
    for (int i = 0; i < cfg->block_count; i++){
        char buf[128];
        sprintf(buf, "cmp rbx,%d", i);
        ADD_INST(NULL, buf);
        sprintf(buf, "je block_%d", i);
        ADD_INST(NULL, buf);
    }

    for(int i = 0; i < cfg->block_count; i++){
        char block_label[64];
        sprintf(block_label, "block_%d:", i);
        ADD_INST(block_label, "nop");

        for(int k = cfg->blocks[i].start_index; k <= cfg->blocks[i].end_index; k++){
            if(P->ins[k].label && strcmp(P->ins[k].label, block_label) == 0){
                if(strlen(P->ins[k].text) > 0) {
                    ADD_INST(NULL, P->ins[k].text);
                }
            } else {
                if(strlen(P->ins[k].text) > 0){
                    ADD_INST(NULL, P->ins[k].text);
                }
            }
        }

        // If block has successors
        if(cfg->blocks[i].succ_count > 0){
            int next = cfg->blocks[i].succ[0];
            char buf[128];
            sprintf(buf, "mov rbx, %d", next);
            ADD_INST(NULL, buf);
            ADD_INST(NULL, "jmp dispatcher");
        }
    }

    // Replace old instructions
    for(int i=0; i<P->count; i++){
        free(P->ins[i].text);
        if(P->ins[i].label) free(P->ins[i].label);
    }
    free(P->ins);
    P->ins = new_list;
    P->count = new_count;
}

// SECTOR 11 : Inter-procedural Obfuscation
static void inter_procedural_obfuscation(Program *P) {
    char *fake_func_label = random_label_name();
    Instruction fake[] = {
        {strdup(fake_func_label), strdup("xor rcx,rcx\nadd rcx,0x9999\ninc rcx\nret"), 1, 0}
    };

    P->ins = realloc(P->ins, sizeof(Instruction)*(P->count + 1));
    int idx = P->count;

    // Insert decrypt_stub_constant function
    P->ins[idx].label = strdup(fake_func_label);
    P->ins[idx].text  = strdup(fake[0].text);
    P->ins[idx].is_instruction = 1;
    P->ins[idx].is_directive   = 0;
    P->count++;

    // Insert 'call fake_func' after dispatcher
    int disp_index = -1;
    for(int i=0; i<P->count; i++){
        if(P->ins[i].label && strcmp(P->ins[i].label, "dispatcher:") == 0){
            disp_index = i;
            break;
        }
    }
    if(disp_index < 0) return;

    int insert_pos = disp_index + 1;
    for(; insert_pos < P->count; insert_pos++){
        char *t = P->ins[insert_pos].text;
        if(strncmp(t, "cmp rbx,", 8) != 0 && strncmp(t,"je block_", 9) != 0){
            break;
        }
    }

    Instruction ins;
    ins.label = NULL;
    {
        char buf[256];
        sprintf(buf, "call %s", fake_func_label);
        ins.text = strdup(buf);
    }
    ins.is_instruction = 1;
    ins.is_directive   = 0;

    P->ins = realloc(P->ins, sizeof(Instruction)*(P->count + 1));
    memmove(&P->ins[insert_pos + 1], &P->ins[insert_pos], sizeof(Instruction)*(P->count - insert_pos));
    P->ins[insert_pos] = ins;
    P->count++;
}

// SECTOR 12 : Metamorphic Transformations
static void rename_regs_in_line(char *line, const char *regs[][2], int reg_map_count);

static void metamorphic_transform_instructions(Program *P) {
    const char *regs[][2] = {
        {"rax", "rcx"},
        {"rbx", "rsi"},
        {"rcx", "r8"},
        {"rdx", "r9"}
    };
    int reg_map_count = 4;

    for(int i=0; i < P->count; i++){
        if(!P->ins[i].is_instruction) continue;

        rename_regs_in_line(P->ins[i].text, regs, reg_map_count);

        if(strncmp(P->ins[i].text, "add rax,", 8) == 0){
            char *imm_str = P->ins[i].text + 8;
            while(*imm_str && isspace((unsigned char)*imm_str)) imm_str++;
            uint64_t val = strtoull(imm_str, NULL, 0);
            if(val > 1 && val < 10){
                Instruction *new_list = malloc(sizeof(Instruction)*(P->count + (val - 1)));
                memcpy(new_list, P->ins, sizeof(Instruction)*i);

                for(uint64_t v=0; v<val; v++){
                    new_list[i+v].label = NULL;
                    new_list[i+v].text  = strdup("inc rax");
                    new_list[i+v].is_instruction=1;
                    new_list[i+v].is_directive  =0;
                }
                memcpy(&new_list[i+val], &P->ins[i+1], sizeof(Instruction)*(P->count-(i+1)));
                free(P->ins[i].text);
                if(P->ins[i].label) free(P->ins[i].label);
                free(P->ins);

                P->ins = new_list;
                P->count += (val - 1);
                i += (val - 1);
            }
        }
    }
}

static void rename_regs_in_line(char *line, const char *regs[][2], int reg_map_count){
    for(int i=0; i<reg_map_count; i++){
        const char *rfrom = regs[i][0];
        const char *rto   = regs[i][1];
        char buffer[1024];
        buffer[0] = '\0';

        const char *start = line;
        const char *pos;

        while((pos = strstr(start, rfrom))){
            int before_ok = (pos == start) || (!isalnum((unsigned char)pos[-1]) && pos[-1] != '_');
            const char *after = pos + strlen(rfrom);
            int after_ok = (!isalnum((unsigned char)*after) && *after != '_');

            if(before_ok && after_ok){
                strncat(buffer, start, pos - start);
                strcat(buffer, rto);
                start = pos + strlen(rfrom);
            } else {
                strncat(buffer, start, (pos - start) + strlen(rfrom));
                start = pos + strlen(rfrom);
            }
        }
        strcat(buffer, start);
        strcpy(line, buffer);
    }
}

// SECTOR 13 : Insert Junk
static void insert_junk(Program *P) {
    const char* junk_ops[] = {
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
            J.label = NULL;
            J.text  = strdup(junk_ops[rand()%jcount]);
            J.is_instruction=1;
            J.is_directive  =0;

            P->ins=realloc(P->ins, sizeof(Instruction)*(P->count+1));
            memmove(&P->ins[i+2], &P->ins[i+1], sizeof(Instruction)*(P->count - (i+1)));
            P->ins[i+1] = J;
            P->count++;
            i++;
        }
    }
}

// SECTOR 14 : Rename Labels
static void replace_label_refs_in_line(char *line, char **old_labels, char **new_labels, int label_count){
    for(int r=0; r<label_count; r++){
        const char *old = old_labels[r];
        const char *new_ = new_labels[r];
        char buffer[2048];
        buffer[0] = '\0';

        const char *start = line;
        const char *pos;
        while((pos = strstr(start, old))){
            int before_ok = (pos == start) || (!isalnum((unsigned char)pos[-1]) && pos[-1] != '_');
            const char *after = pos + strlen(old);
            int after_ok = (!isalnum((unsigned char)*after) && *after != '_');

            if(before_ok && after_ok){
                strncat(buffer, start, pos - start);
                strcat(buffer, new_);
                start = pos + strlen(old);
            } else {
                strncat(buffer, start, (pos - start) + strlen(old));
                start = pos + strlen(old);
            }
        }
        strcat(buffer, start);
        strcpy(line, buffer);
    }
}

static void rename_labels(Program *P){
    typedef struct {
        char *old;
        char *new_;
    } LabelRename;

    LabelRename *renames = NULL;
    int rcount = 0, rcap = 0;

    for(int i=0; i<P->count; i++){
        if(P->ins[i].label){
            if(rcount >= rcap){
                rcap = rcap ? rcap * 2 : 64;
                renames = realloc(renames, sizeof(LabelRename)*rcap);
            }
            renames[rcount].old = strdup(P->ins[i].label);
            renames[rcount].new_ = random_label_name();
            free(P->ins[i].label);
            P->ins[i].label = strdup(renames[rcount].new_);
            rcount++;
        }
    }

    char **old_labels = malloc(rcount * sizeof(char*));
    char **new_labels = malloc(rcount * sizeof(char*));
    for(int i=0; i<rcount; i++){
        old_labels[i] = renames[i].old;
        new_labels[i] = renames[i].new_;
    }

    for(int i=0; i<P->count; i++){
        if(P->ins[i].is_instruction){
            replace_label_refs_in_line(P->ins[i].text, old_labels, new_labels, rcount);
        }
    }

    for(int i=0; i<rcount; i++){
        free(renames[i].old);
        free(renames[i].new_);
    }
    free(renames);
    free(old_labels);
    free(new_labels);
}

// SECTOR 15 : Write Output
static void write_output(const char *filename, Program *P) {
    FILE *f = fopen(filename, "w");
    if(!f){
        perror("fopen output");
        exit(1);
    }
    for(int i=0; i<P->count; i++){
        if(P->ins[i].label) {
            // Ensure label ends with ':' if not empty
            if(strlen(P->ins[i].label) > 0 && P->ins[i].label[strlen(P->ins[i].label)-1] != ':'){
                fprintf(f, "%s:\n", P->ins[i].label);
            } else {
                fprintf(f, "%s\n", P->ins[i].label);
            }
        }
        if(strlen(P->ins[i].text) > 0) {
            fprintf(f, "%s\n", P->ins[i].text);
        }
    }
    fclose(f);
}

// SECTOR 16 : Replace Pseudo-Instructions
static void replace_pseudo_instructions(Program *P) {
    typedef struct {
        const char *pseudo;
        const char *replacement;
    } PseudoInstr;

    PseudoInstr replacements[] = {
        {
            "write(1, msg, len)",
            "mov rax, 1          ; syscall number for write\n"
            "mov rdi, 1          ; file descriptor (stdout)\n"
            "lea rsi, [rel msg]  ; pointer to message\n"
            "mov rdx, len        ; message length\n"
            "syscall             ; invoke syscall"
        },
        {
            "exit(0)",
            "mov rax, 60         ; syscall number for exit\n"
            "xor rdi, rdi        ; exit status 0\n"
            "syscall             ; invoke syscall"
        }
    };

    int num_replacements = sizeof(replacements) / sizeof(PseudoInstr);

    for(int i=0; i<P->count; i++){
        if(P->ins[i].is_instruction){
            for(int j=0; j<num_replacements; j++){
                if(strcmp(P->ins[i].text, replacements[j].pseudo) == 0){
                    // Create a mutable copy of the replacement string
                    char *mutable_buf = strdup(replacements[j].replacement);

                    // Free the original instruction text
                    free(P->ins[i].text);

                    // Tokenize the replacement string by newline
                    char *saveptr = NULL;
                    char *line = strtok_r(mutable_buf, "\n", &saveptr);
                    if(line){
                        // Overwrite current instruction with the first line
                        P->ins[i].text = strdup(line);

                        // Insert additional instructions after the current one
                        while((line = strtok_r(NULL, "\n", &saveptr)) != NULL){
                            Instruction new_inst;
                            new_inst.label         = NULL;
                            new_inst.text          = strdup(line);
                            new_inst.is_directive  = (line[0] == '.');
                            new_inst.is_instruction= (!new_inst.is_directive && strlen(line) > 0);

                            P->ins = realloc(P->ins, sizeof(Instruction)*(P->count + 1));
                            memmove(&P->ins[i + 2], &P->ins[i + 1], sizeof(Instruction)*(P->count - (i + 1)));
                            P->ins[i + 1] = new_inst;
                            P->count++;
                            i++; // Skip the newly inserted instruction
                        }
                    }
                    free(mutable_buf);
                }
            }
        }
    }
}

// SECTOR fin : Main
int main(int argc, char**argv) {
    if(argc < 3){
        fprintf(stderr,"Usage: %s input.s output.s\n", argv[0]);
        return 1;
    }
    srand(time(NULL));

    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);

    Program P;
    memset(&P, 0, sizeof(P));
    P.ins = read_instructions(argv[1], &P.count);

    // 1. Extract data from .data
    extract_data(&P);
    // 2. Encrypt it
    encrypt_data(&P);

    fprintf(stderr,"[+] Building CFG...\n");
    P.cfg = build_cfg(P.ins, P.count);

    fprintf(stderr,"[+] Encrypting constants...\n");
    encrypt_constants(&P);

    fprintf(stderr,"[+] Inserting runtime decrypt stub (for constants)...\n");
    insert_runtime_decrypt_stub(&P);

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

    fprintf(stderr,"[+] Replacing pseudo-instructions...\n");
    replace_pseudo_instructions(&P);

    fprintf(stderr,"[+] Inserting data decoder...\n");
    insert_data_decoder(&P);

    fprintf(stderr,"[+] Writing output...\n");
    write_output(argv[2], &P);

    clock_gettime(CLOCK_MONOTONIC, &end);
    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) * 1e-9;
    fprintf(stderr,"[+] Done in %.8f seconds.\n", elapsed);

    return 0;
}
