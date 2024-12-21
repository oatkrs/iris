; sample.asm

section .data
msg db "Hello, IRIS!", 0x0a
len equ $ - msg

section .text
global _start
_start:
    ; Write syscall: write(1, msg, len)
    mov rax, 1          ; syscall number for write
    mov rdi, 1          ; file descriptor (stdout)
    lea rsi, [rel msg]  ; pointer to message
    mov rdx, len        ; message length
    syscall             ; invoke syscall

    ; Exit syscall: exit(0)
    mov rax, 60         ; syscall number for exit
    xor rdi, rdi        ; exit status 0
    syscall             ; invoke syscall
