/* Where Spire keeps its tables.
 *
 * On x86-64 (Linux and Windows), every table the inner loops read sits at a fixed address
 * between 1 and 2 GB, reserved at startup (with mmap or VirtualAlloc): high enough to be clear
 * of the program and its heap, low enough for a 32-bit constant. The loops can then name a
 * table as a constant inside the instruction, as in
 * `mov eax, [rax*4 + PAIR_CHAIN]`, instead of holding its address in a register. On x86-64
 * with only 15 usable registers, that is what lets four chains run in one loop.
 *
 * This header is included by spire.c and by loops.S (which the C preprocessor also reads).
 *
 * A "slot" is one entry of a machine's table: the slot for state s reading byte b is
 * row(s) + code(b), where row(s) is the state's first slot and code(b) numbers the bytes by
 * how often they occur. Both machines (the pairs and the top tower) number their slots from 0.
 */
#ifndef SPIRE_LAYOUT_H
#define SPIRE_LAYOUT_H

#define BYTE_CODE   0x42000000  /* uint32 [256]      byte -> code (the column within a row)  */
#define POWER_OF_P  0x42100000  /* uint64 [65536]    P^L                                      */
#define PAIR_CHAIN  0x44000000  /* uint32 per slot   tag | next << 16  (the pairs)            */
#define TOP_CHAIN   0x45000000  /* uint32 per slot   tag | next << 16  (the top tower)        */
#define PAIR_SYMS   0x48000000  /* uint64 per slot   symbols made << 8 | 2 * their number     */
#define TOP_STEP    0x58000000  /* 32 bytes per slot {L | dm << 24, (P-1) B, (P-1) C + dm,
                                                      dnu - dm}  (see "The top's hash")        */
#define TOP_BLOCKS  0x68000000  /* uint64 per slot   block list offset | count << 32 (rows)   */

#define RECORDS_PER_CHAIN 4096  /* the chain loops record at most this many steps per call   */

#endif
