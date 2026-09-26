/* Spire's inner loops, in x86-64 assembly (GNU as, Intel syntax), for Windows and for
 * Linux and other System V systems.
 *
 * Why assembly. A chain of table lookups is a relay: each lookup's address depends on the
 * previous lookup's result, so one chain waits about 15 cycles per step for the cache. Running
 * four independent chains in one loop hides that wait, but only if every chain's state lives
 * in a register. The C compiler kept spilling some of it to the stack, putting a store and a
 * load on the critical path; here the register assignment is by hand.
 *
 * Why two loops. Each step also has work that depends on its lookup (packing the symbols it
 * makes, or updating the hash). If that work sits in the chain loop, it clogs the processor's
 * schedulers while the chains wait. So `chains4` runs the four chains alone, recording each
 * step's slot, and `pack2` or `hash2` then does the work from the records, where nothing waits.
 *
 * The chain loop is assembled twice, once for each table (the pairs and the top tower), by the
 * macro CHAINS4. The tables' addresses come from layout.h.
 *
 * The bodies are written for the Windows x64 convention: arguments in rcx, rdx, r8, r9 and the
 * fifth on the stack; rbx, rbp, rdi, rsi and r12-r15 preserved (the prologue pushes all
 * eight). Under System V (Linux), where the arguments come in rdi, rsi, rdx, rcx and r8, the
 * prologue moves them into those registers first and keeps the fifth in the frame.
 */
#include "layout.h"

    .intel_syntax noprefix
    .text

#ifdef _WIN32
#define PROLOGUE(name) \
    .globl name; .def name; .scl 2; .type 32; .endef; .seh_proc name; name: \
    push rbx; .seh_pushreg rbx; push rbp; .seh_pushreg rbp; push rdi; .seh_pushreg rdi; \
    push rsi; .seh_pushreg rsi; push r12; .seh_pushreg r12; push r13; .seh_pushreg r13; \
    push r14; .seh_pushreg r14; push r15; .seh_pushreg r15; sub rsp, 40; .seh_stackalloc 40; \
    .seh_endprologue
#define EPILOGUE \
    add rsp, 40; pop r15; pop r14; pop r13; pop r12; pop rsi; pop rdi; pop rbp; pop rbx; ret; \
    .seh_endproc
#define ARG5 [rsp + 144]                     /* the fifth argument, after the prologue */
#else
#define PROLOGUE(name) \
    .globl name; .type name, @function; name: \
    push rbx; push rbp; push rdi; push rsi; push r12; push r13; push r14; push r15; sub rsp, 40; \
    mov [rsp + 32], r8; mov r9, rcx; mov r8, rdx; mov rdx, rsi; mov rcx, rdi
#define EPILOGUE \
    add rsp, 40; pop r15; pop r14; pop r13; pop r12; pop rsi; pop rdi; pop rbp; pop rbx; ret
#define ARG5 [rsp + 32]                      /* the fifth argument, kept by the prologue */
#endif
#define RECORD_STRIDE (2 * RECORDS_PER_CHAIN)  /* bytes between the four record arrays */


/* uint32_t pair_chains4 / top_chains4(uint64_t row[4], const uint8_t *const in[4],
 *                                     uint16_t *rec, uint32_t K);
 *
 * Runs K steps of four chains. A chain's whole state is its row (the first slot of its state).
 * Step: slot = row + code[input byte]; w = chain[slot]; if the low half of w (the slot's tag,
 * the row it belongs to) is not the chain's row, the transition is not in the table: stop
 * before this step, so that the caller does it the slow way. Otherwise row = w >> 16 (the next
 * state's row), and the slot is recorded in rec[j * RECORDS_PER_CHAIN + step].
 * Returns the number of steps done; row[] is updated.
 *
 * Registers:  r12 r13 r14 r15  the four rows          r10  input of chain 0 (advances)
 *             rbx rbp rdi      in[1..3] - in[0]         r11  end of chain 0's input
 *             rsi              next record              rax rcx rdx r8  one slot per chain
 */
.macro CHAINS4 name, chain
PROLOGUE(\name)
    mov [rsp], rcx                      /* row[] */
    mov r12, [rcx]
    mov r13, [rcx + 8]
    mov r14, [rcx + 16]
    mov r15, [rcx + 24]
    mov r10, [rdx]
    mov rbx, [rdx + 8]
    sub rbx, r10
    mov rbp, [rdx + 16]
    sub rbp, r10
    mov rdi, [rdx + 24]
    sub rdi, r10
    mov [rsp + 8], r10                  /* where the input started */
    mov rsi, r8
    mov r11d, r9d
    add r11, r10
    cmp r10, r11
    je .Lchains_done\@
    .p2align 4
.Lchains_loop\@:
    movzx eax, byte ptr [r10]           /* the four input bytes */
    movzx ecx, byte ptr [r10 + rbx]
    movzx edx, byte ptr [r10 + rbp]
    movzx r8d, byte ptr [r10 + rdi]
    mov eax, dword ptr [rax*4 + BYTE_CODE]
    mov ecx, dword ptr [rcx*4 + BYTE_CODE]
    mov edx, dword ptr [rdx*4 + BYTE_CODE]
    mov r8d, dword ptr [r8*4 + BYTE_CODE]
    add rax, r12                        /* the four slots */
    add rcx, r13
    add rdx, r14
    add r8, r15
    mov [rsi], ax                       /* recorded now; ignored if the step is not taken */
    mov [rsi + RECORD_STRIDE], cx
    mov [rsi + 2*RECORD_STRIDE], dx
    mov [rsi + 3*RECORD_STRIDE], r8w
    mov eax, dword ptr [rax*4 + \chain]
    mov ecx, dword ptr [rcx*4 + \chain]
    mov edx, dword ptr [rdx*4 + \chain]
    mov r8d, dword ptr [r8*4 + \chain]
    cmp ax, r12w                        /* all four tags checked before any chain moves */
    jne .Lchains_done\@
    cmp cx, r13w
    jne .Lchains_done\@
    cmp dx, r14w
    jne .Lchains_done\@
    cmp r8w, r15w
    jne .Lchains_done\@
    shr eax, 16                         /* the next rows */
    mov r12d, eax
    shr ecx, 16
    mov r13d, ecx
    shr edx, 16
    mov r14d, edx
    shr r8d, 16
    mov r15d, r8d
    add rsi, 2
    inc r10
    cmp r10, r11
    jne .Lchains_loop\@
.Lchains_done\@:
    mov rcx, [rsp]
    mov [rcx], r12
    mov [rcx + 8], r13
    mov [rcx + 16], r14
    mov [rcx + 24], r15
    mov rax, r10
    sub rax, [rsp + 8]                  /* steps done */
EPILOGUE
.endm
CHAINS4 pair_chains4, PAIR_CHAIN
CHAINS4 top_chains4, TOP_CHAIN


/* void pair_pack2(uint64_t st0[3], uint64_t st1[3], const uint16_t *rec0, const uint16_t *rec1,
 *                 uint32_t K);   st = {carry, bits, output pointer}
 *
 * Appends the symbols of K recorded steps of two pairs to their outputs, two bits a symbol.
 * A step makes up to 28 symbols (56 bits); with the 0-7 bits carried from before, they fit in
 * one 64-bit word, which is stored whole; the output pointer then advances by the complete
 * bytes, and the rest is carried:
 *     pending = carry | symbols << bits;   total = bits + 2 len;   store pending at out;
 *     out += total / 8;   carry = pending >> (total & ~7);   bits = total & 7.
 *
 * Registers:  r12 rbx rdi  carry, bits, out of pair 0     r10  record of pair 0 (advances)
 *             r13 rbp rsi  carry, bits, out of pair 1     r11  rec1 - rec0     r14  end
 */
PROLOGUE(pair_pack2)
    mov [rsp], rcx
    mov [rsp + 8], rdx
    mov r12, [rcx]
    mov rbx, [rcx + 8]
    mov rdi, [rcx + 16]
    mov r13, [rdx]
    mov rbp, [rdx + 8]
    mov rsi, [rdx + 16]
    mov r10, r8
    mov r11, r9
    sub r11, r8
    mov r14d, dword ptr ARG5
    lea r14, [r10 + r14*2]
    cmp r10, r14
    je .Lpack_done
    .p2align 4
.Lpack_loop:
    movzx eax, word ptr [r10]           /* the two recorded slots */
    movzx ecx, word ptr [r10 + r11]
    mov rdx, qword ptr [rax*8 + PAIR_SYMS]      /* pair 0 */
    movzx r8d, dl                       /* 2 len */
    shr rdx, 8                          /* the symbols */
    shlx rdx, rdx, rbx
    or rdx, r12                         /* pending */
    add r8, rbx                         /* total */
    mov [rdi], rdx
    mov r9, r8
    shr r9, 3
    add rdi, r9
    mov rbx, r8
    and rbx, 7
    and r8d, 56
    shrx r12, rdx, r8
    mov rdx, qword ptr [rcx*8 + PAIR_SYMS]      /* pair 1, the same */
    movzx r8d, dl
    shr rdx, 8
    shlx rdx, rdx, rbp
    or rdx, r13
    add r8, rbp
    mov [rsi], rdx
    mov r9, r8
    shr r9, 3
    add rsi, r9
    mov rbp, r8
    and rbp, 7
    and r8d, 56
    shrx r13, rdx, r8
    add r10, 2
    cmp r10, r14
    jne .Lpack_loop
.Lpack_done:
    mov rcx, [rsp]
    mov rdx, [rsp + 8]
    mov [rcx], r12
    mov [rcx + 8], rbx
    mov [rcx + 16], rdi
    mov [rdx], r13
    mov [rdx + 8], rbp
    mov [rdx + 16], rsi
EPILOGUE


/* void top_hash2(uint64_t st0[3], uint64_t st1[3], const uint16_t *rec0, const uint16_t *rec1,
 *                uint32_t K);   st = {M, D, F}
 *
 * Applies K recorded steps of two top towers to their counters and hash:
 *     M = m << 24 | columns,   D = (n + U) - m,   F = (P - 1) H + m,
 * and a step with slot data {L | dm << 24, (P-1) B, (P-1) C + dm, dnu - dm} does
 *     F <- F P^L + D (P-1) B + (P-1) C + dm      (two multiplications)
 *     M += dm << 24 | L,    D += dnu - dm.
 * The columns ride in M's low 24 bits (the caller keeps K * L below 2^24).
 *
 * Registers:  r12 rdi rbx  M, D, F of tower 0     r10  record of tower 0 (advances)
 *             r13 rsi rbp  M, D, F of tower 1     r11  rec1 - rec0     r14  end
 */
PROLOGUE(top_hash2)
    mov [rsp], rcx
    mov [rsp + 8], rdx
    mov r12, [rcx]
    mov rdi, [rcx + 8]
    mov rbx, [rcx + 16]
    mov r13, [rdx]
    mov rsi, [rdx + 8]
    mov rbp, [rdx + 16]
    mov r10, r8
    mov r11, r9
    sub r11, r8
    mov r14d, dword ptr ARG5
    lea r14, [r10 + r14*2]
    cmp r10, r14
    je .Lhash_done
    .p2align 4
.Lhash_loop:
    movzx eax, word ptr [r10]           /* the two recorded slots, times 32 bytes */
    movzx ecx, word ptr [r10 + r11]
    shl rax, 5
    shl rcx, 5
    mov rdx, qword ptr [rax + TOP_STEP]         /* tower 0: L | dm << 24 */
    mov r8, rdi
    imul r8, qword ptr [rax + TOP_STEP + 8]     /* D (P-1) B */
    add r8, qword ptr [rax + TOP_STEP + 16]     /* + (P-1) C + dm */
    add rdi, qword ptr [rax + TOP_STEP + 24]    /* D += dnu - dm */
    add r12, rdx                                /* m += dm, columns += L */
    movzx eax, dx                               /* L */
    imul rbx, qword ptr [rax*8 + POWER_OF_P]    /* F P^L */
    add rbx, r8
    mov rdx, qword ptr [rcx + TOP_STEP]         /* tower 1, the same */
    mov r8, rsi
    imul r8, qword ptr [rcx + TOP_STEP + 8]
    add r8, qword ptr [rcx + TOP_STEP + 16]
    add rsi, qword ptr [rcx + TOP_STEP + 24]
    add r13, rdx
    movzx ecx, dx
    imul rbp, qword ptr [rcx*8 + POWER_OF_P]
    add rbp, r8
    add r10, 2
    cmp r10, r14
    jne .Lhash_loop
.Lhash_done:
    mov rcx, [rsp]
    mov rdx, [rsp + 8]
    mov [rcx], r12
    mov [rcx + 8], rdi
    mov [rcx + 16], rbx
    mov [rdx], r13
    mov [rdx + 8], rsi
    mov [rdx + 16], rbp
EPILOGUE

#ifndef _WIN32
    .section .note.GNU-stack, "", @progbits
#endif
