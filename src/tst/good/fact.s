	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_fact:
	pushq %rbp
	movq %rsp, %rbp
	movq 16(%rbp), %rdi
	pushq %rdi
	movq $1, %rdi
	popq %rax
	cmpq %rdi, %rax
	jle L_3
	movq $0, %rdi
	jmp L_4
L_3:
	movq $1, %rdi
L_4:
	testq %rdi, %rdi
	jne L_1
	jmp L_2
L_1:
	movq $1, %rdi
	jmp E_fact
L_2:
	movq 16(%rbp), %rdi
	pushq %rdi
	movq 16(%rbp), %rdi
	pushq %rdi
	movq $1, %rdi
	movq %rdi, %rax
	popq %rdi
	subq %rax, %rdi
	pushq %rdi
	call F_fact
	addq $8, %rsp
	movq %rdi, %rax
	popq %rdi
	imulq %rax, %rdi
	jmp E_fact
E_fact:
	movq %rbp, %rsp
	popq %rbp
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	movq $3, %rdi
	pushq %rdi
	call F_fact
	addq $8, %rsp
	call print_int
E_main:
	movq %rbp, %rsp
	popq %rbp
	ret

print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
print_string: 
	      movq %rdi, %rsi
	      movq $S_string, %rdi
	      xorq %rax, %rax
	      call printf
	      ret
	.data
S_int:
	.string "%ld"
S_string:
	.string "%s"
