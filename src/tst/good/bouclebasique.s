	.text
	.globl	main
main:
	call F_main
	xorq %rax, %rax
	ret
F_main:
	pushq %rbp
	movq %rsp, %rbp
	pushq $0
L_1:
	movq -8(%rbp), %rdi
	pushq %rdi
	movq $10, %rdi
	popq %rax
	cmpq %rdi, %rax
	jle L_3
	movq $0, %rdi
	jmp L_4
L_3:
	movq $1, %rdi
L_4:
	testq %rdi, %rdi
	jz L_2
	movq $S_1, %rdi
	call print_string
	movq -8(%rbp), %rdi
	incq %rdi
	pushq %rdi
	leaq -8(%rbp), %rdi
	popq %rbx
	movq %rbx, 0(%rdi)
	jmp L_1
L_2:
	popq %rdi
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
S_1:
	.string "a"
