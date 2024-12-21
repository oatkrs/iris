.intel_syntax noprefix
.global _start
_start:
    mov rax, 1         ; syscall: write
    mov rdi, 1         ; fd=1 (stdout)
    lea rsi, [rip+msg] ; buffer
    mov rdx, len       ; length
    syscall

    mov rax, 60        ; syscall: exit
    mov rdi,0
    syscall

section .rodata
msg: db "Hello, IRIS!", 0x0a
len = . - msg
