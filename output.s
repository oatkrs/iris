.text
.global _start
__zbLUuEeE__:
mov rbx,0
jmp __lGrl9ACs__
__lGrl9ACs__:
cmp rbx,0
xor rdx,rdx
je __BGr0i6Lv__
cmp rbx,1
je __CLuTgj0T__
cmp rbx,2
je __ABnuFFwo__
cmp rbx,3
je __MdPLbP2b__
cmp rbx,4
je __WjR2fbli__
push rax
pop rax
call __mUzG3pX3__
__BGr0i6Lv__:
nop
.intel_syntax noprefix
.global _start
__CLuTgj0T__:
nop
__ABnuFFwo__:
nop
write
xor rdx,rdx
mov rdi, 1         ; fd=1 (stdout)
lea rsi, [rip+msg] ; buffer
mov r9, len       ; length
syscall
__MdPLbP2b__:
nop
exit
mov rdi,0
syscall
__WjR2fbli__:
nop
len = . - msg
__mUzG3pX3__:
xor rcx,rcx
add rcx,0x9999
inc rcx
ret
xchg rax,rax
