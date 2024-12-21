section .text
.global _start
__zUNNnjLC__:
mov rbx,0
jmp dispatcherq
__RcH392C2__:
cmp rbx,0
je block_0
cmp rbx,1
je block_1
cmp rbx,2
je block_2
cmp rbx,3
je block_3
call __q810ILE1__
__Rv6pKJWO__:
nop
section .data
msg db "Hello, IRIS!", 0x0a
len equ $ - msg
section .text
global _start
__vpXolDDa__:
nop
__VQl8xuAE__:
nop
mov rax,1
mov rdi,1
lea rsi,[rel msg]
mov rdx,len
syscall
mov r8, 1
mov rdi, 1
lea rsi, [rel msg]
mov r9, len
syscall
__MG7K67CN__:
nop
mov rax,60
xor rdi,rdi
syscall
mov r8, 60
xor rdi, rdi
syscall
__q810ILE1__:
xor rcx,rcx
add rcx,0x1337
inc rcx
ret
