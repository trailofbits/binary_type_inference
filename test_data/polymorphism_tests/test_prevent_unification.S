.global id
.global alias_id
.global caller1
.global caller2


id:
    mov rax, rdi
    ret

alias_id:
    mov rdi, rdi
    call id
    mov rax, rax
    ret

caller1:
    mov rdi, rdi
    call alias_id
    mov rax, rax
    ret

caller2:
    mov rdi, rdi
    call alias_id
    mov rax, rax
    ret

