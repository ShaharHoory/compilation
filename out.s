MALLOC rax, 8
mov qword rbx, [rbp + 8 * 2]

mov [extEnv], rax
MALLOC rdx, [rbp + 8 * 3]
mov [rax], rdx
move rdx, [rax]
mov rbx, [rbp + 8*(4 + 0)]
mov [rdx + 0], rbx

MALLOC rax, 2*8
mov rdx, [extEnv]
mov [rax], rdx
mov rdx,Lcode0
jmp Lcont0
Lcode0:
 push rbp
mov rbp, rsp
mov rax, qword [rbp + 8*(4 + 0)]
leave
ret
Lcont0:
 