memcpy disassembly — basic blocks + semantics theorems
========================================================

259 instructions @ 0x002008f8..0x00200d00.  Every block has a `Triple`
proof in `MemcpyProof/Hoare/`.  Below: per-block disassembly with the
file and the post-condition `R_*` for each block inlined as comments.

Convention (RISC-V RV32I, calling convention):
  x10 = a0 = dst,  x11 = a1 = src,  x12 = a2 = n  (memcpy(dst, src, n))
  x13..x17 = a3..a7 = scratch regs used by the loop
  Block terminators: bne / beq / bltu / jal / jalr  (no fall-through is
  marked explicitly; the line after a terminator is the next block's
  entry PC).


===============================================================================
B1  block_align_check   —  Hoare/BlockPrefix.lean
PCs 0x002008f8..0x00200908  (5 instr, bne terminator)
===============================================================================
  0x2008f8:  0035f693   andi  a3, a1, 3        ; a3 := src & 3
  0x2008fc:  0016b693   sltiu a3, a3, 1        ; a3 := (src&3 == 0)
  0x200900:  00163713   sltiu a4, a2, 1        ; a4 := (n == 0)
  0x200904:  00e6e6b3   or    a3, a3, a4       ; a3 := aligned ∨ n=0
  0x200908:  0e069c63   bne   a3, zero, +248   ; → 0x200a00 (B11) if either

  R_block_align_check s s' :=
    s'.pc = s.pc + 16 ∧
    let aligned := (if 0 < (a1 & 3) then 1 else 0)
    let nzero   := (if 0 < a2     then 0 else 1)
    getReg s' 13 = aligned ∨ nzero ∧                  -- ≠0 iff src aligned OR n=0
    s'.mem = s.mem ∧ <frame on regs ≠ 13, 14>


===============================================================================
B2  block_byte_prefix_body   —  Hoare/Blocks/BytePrefix.lean
PCs 0x0020090c..0x00200944  (15 instr, bne terminator)
The 14 body instrs are the byte-prefix loop body.  bne loops back to
0x200914 (skipping the first 2 setup instrs).
===============================================================================
  0x20090c:  00158793   addi  a5, a1, 1        ; (SETUP) a5 := src+1
  0x200910:  00050813   addi  a6, a0, 0        ; (SETUP) a6 := dst
  -- bne branch target ↓ ----------------------------------------------------
  0x200914:  00058883   lb    a7, 0(a1)        ; a7 := signExt(mem[src])
  0x200918:  00158713   addi  a4, a1, 1        ; a4 := src+1
  0x20091c:  00180693   addi  a3, a6, 1        ; a3 := (cur dst) + 1
  0x200920:  01180023   sb    a7, 0(a6)        ; *(cur dst) := a7  ⟵ byte copied
  0x200924:  fff60613   addi  a2, a2, -1       ; n--
  0x200928:  0037f593   andi  a1, a5, 3        ; a1 := (a5) & 3
  0x20092c:  00b035b3   sltu  a1, zero, a1     ; a1 := (a5 & 3 ≠ 0) ? 1 : 0
  0x200930:  00c03833   sltu  a6, zero, a2     ; a6 := (a2 ≠ 0)     ? 1 : 0
  0x200934:  0105f8b3   and   a7, a1, a6       ; a7 := continue-flag
  0x200938:  00178793   addi  a5, a5, 1        ; a5 := a5+1
  0x20093c:  00070593   addi  a1, a4, 0        ; a1 := a4 (= src+1 next iter)
  0x200940:  00068813   addi  a6, a3, 0        ; a6 := a3 (= dst+1)
  0x200944:  fc0898e3   bne   a7, zero, -48    ; → 0x200914  (loop back)

  R_block_byte_prefix_body s s' :=  (flat post for the 14 body instrs)
    let ext = signExt (loadByte s a1) 7
    s'.pc = s.pc + 56 ∧
    a1 ← a1+1   a2 ← a2-1
    a3 ← a0+1   a4 ← a1+1   a5 ← a1+2   a6 ← a0+1
    a7 ← ((a1+1)&3≠0) ∧ (a2-1≠0)
    mem ← storeByte s a0 ext.toUInt8 ∧
    <frame on regs ≠ 11..17>

  -- Plus loop-aware split (BytePrefix.lean, also Hoare/Blocks/LoopBytePrefix.lean):
  --   block_byte_prefix_setup = first 2 instrs (runs once)
  --     R: a5 ← a1+1, a6 ← a0, mem unchanged
  --   block_byte_prefix_main  = last 12 instrs (runs every loop iter)
  --     R parametric in entry x15, x16

  -- Loop semantics (LoopBytePrefix.lean):
  --   loop_byte_prefix_one_iter_triple — proves the 12+bne effect parametrically
  --   loop_byte_prefix_full_correct    — full K-iter loop (K ∈ {1,2,3});
  --                                       K=1 case PROVED, K=2,3 cases sorry'd


===============================================================================
B3..B7  alignment dispatch  —  Hoare/Blocks/Simple.lean
After the byte-prefix loop, src is now aligned; figure out which case.
===============================================================================
  ─────── B3 ─── 0x00200948 → beq @ 0x20094c (→ 0x200a10 = B12 setup)
  0x200948:  0036f593   andi  a1, a3, 3        ; a1 := (cur dst)&3
  0x20094c:  0c058263   beq   a1, zero, +196   ; → 0x200a10 if dst aligned
    R:  a1 ← a3 & 3,  s'.pc = s.pc + 4

  ─────── B4 ─── 0x00200950 → bltu @ 0x200954
  0x200950:  02000793   addi  a5, zero, 32     ; a5 := 32
  0x200954:  22f66e63   bltu  a2, a5, +572     ; → 0x200b90 if n < 32 (byte tail)
    R:  a5 ← 32,  s'.pc = s.pc + 4

  ─────── B5 ─── 0x00200958 → beq @ 0x20095c
  0x200958:  00300793   addi  a5, zero, 3      ; a5 := 3
  0x20095c:  12f58663   beq   a1, a5, +300     ; → 0x200a88 if dst-align = 3
    R:  a5 ← 3,  s'.pc = s.pc + 4

  ─────── B6 ─── 0x00200960 → beq @ 0x200964
  0x200960:  00200793   addi  a5, zero, 2      ; a5 := 2
  0x200964:  1af58263   beq   a1, a5, +420     ; → 0x200b08 if dst-align = 2
    R:  a5 ← 2,  s'.pc = s.pc + 4

  ─────── B7 ─── 0x00200968 → bne @ 0x20096c
  0x200968:  00100793   addi  a5, zero, 1      ; a5 := 1
  0x20096c:  22f59263   bne   a1, a5, +548     ; → 0x200b90 if dst-align ≠ 1
    R:  a5 ← 1,  s'.pc = s.pc + 4


===============================================================================
B8  block_F_unaligned1_setup   —  Hoare/Blocks/Setups.lean
PCs 0x00200970..0x00200994  (10 instr).  First-iteration preamble for the
unaligned-by-1 word-loop (dst align = 1).
===============================================================================
  0x200970:  00072783   lw    a5, 0(a4)        ; a5 := word[src]
  0x200974:  00f68023   sb    a5, 0(a3)        ; *(dst+0) := lo8(a5)
  0x200978:  0087d593   srli  a1, a5, 8        ; a1 := a5 >> 8
  0x20097c:  00b680a3   sb    a1, 1(a3)        ; *(dst+1) := lo8(a1)
  0x200980:  0107d813   srli  a6, a5, 16       ; a6 := a5 >> 16
  0x200984:  00368593   addi  a1, a3, 3        ; a1 := dst+3
  0x200988:  01068123   sb    a6, 2(a3)        ; *(dst+2) := lo8(a6)
  0x20098c:  ffd60613   addi  a2, a2, -3       ; n -= 3
  0x200990:  01070693   addi  a3, a4, 16       ; a3 := src+16  (NB: a3 reused as src-ptr)
  0x200994:  01000713   addi  a4, zero, 16     ; a4 := 16  (loop-tail threshold)

  R: writes 3 src bytes to dst+0..2, sets a3 ← src+16, a4 ← 16, decrements a2.
     Falls through to B9.


===============================================================================
B9  block_F_unaligned1   —  Hoare/Blocks/UnalignedBody.lean
PCs 0x00200998..0x002009f4  (24 instr).  Loop body for dst-align=1.
= `mk_block_F_unaligned 24 8`.  Loops on (src not-aligned, 16-byte chunks).
===============================================================================
  0x200998:  ff46a803   lw    a6, -12(a3)      ; load words at a3-12, -8, -4, 0
  0x20099c:  0187d793   srli  a5, a5, 24
  0x2009a0:  00881893   slli  a7, a6, 8
  0x2009a4:  ff86a283   lw    t0, -8(a3)
  0x2009a8:  00f8e7b3   or    a5, a7, a5
  0x2009ac:  00f5a023   sw    a5, 0(a1)        ; store reconstructed word
  0x2009b0:  01885793   srli  a5, a6, 24
  0x2009b4:  00829813   slli  a6, t0, 8
  0x2009b8:  ffc6a883   lw    a7, -4(a3)
  0x2009bc:  00f867b3   or    a5, a6, a5
  0x2009c0:  00f5a223   sw    a5, 4(a1)
  0x2009c4:  0182d813   srli  a6, t0, 24
  0x2009c8:  00889293   slli  t0, a7, 8
  0x2009cc:  0006a783   lw    a5, 0(a3)
  0x2009d0:  0102e833   or    a6, t0, a6
  0x2009d4:  0105a423   sw    a6, 8(a1)
  0x2009d8:  0188d813   srli  a6, a7, 24
  0x2009dc:  00879893   slli  a7, a5, 8
  0x2009e0:  0108e833   or    a6, a7, a6
  0x2009e4:  0105a623   sw    a6, 12(a1)
  0x2009e8:  01058593   addi  a1, a1, 16       ; dst += 16
  0x2009ec:  ff060613   addi  a2, a2, -16      ; n   -= 16
  0x2009f0:  01068693   addi  a3, a3, 16       ; src += 16
  0x2009f4:  fac762e3   bltu  a4, a2, -92      ; → 0x200998 if n > 16 (loop)

  R: 16 bytes copied per iter via 4 word-loads + 4 word-stores with shift-merge.
     Proved parametrically via `mk_block_F_unaligned 24 8` (5-chunk RComp).


===============================================================================
B10  block_B10   —  Hoare/Blocks/Simple.lean
PCs 0x002009f8..0x002009fc  (2 instr).
===============================================================================
  0x2009f8:  ff368713   addi  a4, a3, -13      ; a4 := a3 - 13
  0x2009fc:  1900006f   jal   zero, +400       ; → 0x200b8c (B25 tail dispatch)
    R: a4 ← a3 + 0xFFFFFFF3,  pc → 0x200b8c


===============================================================================
B11  block_setup_align   —  Hoare/Blocks/Setups.lean
PCs 0x00200a00..0x00200a0c  (4 instr, bne terminator).
===============================================================================
  0x200a00:  00050693   addi  a3, a0, 0        ; a3 := dst
  0x200a04:  00058713   addi  a4, a1, 0        ; a4 := src
  0x200a08:  0036f593   andi  a1, a3, 3        ; a1 := dst & 3
  0x200a0c:  f40592e3   bne   a1, zero, -188   ; → 0x20094c (back to B3 dispatch)

  R: a3 ← a0, a4 ← a1, a1 ← a3 & 3.  (Bne taken if dst was not aligned.)


===============================================================================
B12  block_B12   —  Hoare/Blocks/Simple.lean
PCs 0x00200a10..0x00200a14  (2 instr, bltu terminator).
===============================================================================
  0x200a10:  01000593   addi  a1, zero, 16
  0x200a14:  02b66c63   bltu  a2, a1, +56      ; → 0x200a4c if n < 16
    R: a1 ← 16


===============================================================================
B13/B14  block_F_first / block_F_iter   —  Hoare/Blocks/AlignedLoop.lean
PCs 0x00200a18..0x00200a48.  Aligned 16-byte fast path.
B13 = B14 with one-instr preamble `addi a1, zero, 15`.
===============================================================================
  0x200a18:  00f00593   addi  a1, zero, 15     ; (B13 preamble) a1 := 15
  -- ↓ B14 loop body ↓
  0x200a1c:  00072783   lw    a5, 0(a4)
  0x200a20:  00472803   lw    a6, 4(a4)
  0x200a24:  00872883   lw    a7, 8(a4)
  0x200a28:  00c72283   lw    t0, 12(a4)       ; 4 word loads from src
  0x200a2c:  00f6a023   sw    a5, 0(a3)
  0x200a30:  0106a223   sw    a6, 4(a3)
  0x200a34:  0116a423   sw    a7, 8(a3)
  0x200a38:  0056a623   sw    t0, 12(a3)       ; 4 word stores to dst
  0x200a3c:  01070713   addi  a4, a4, 16       ; src += 16
  0x200a40:  ff060613   addi  a2, a2, -16      ; n   -= 16
  0x200a44:  01068693   addi  a3, a3, 16       ; dst += 16
  0x200a48:  fcc5eae3   bltu  a1, a2, -44      ; → 0x200a1c if n > 15 (loop)

  R: 16 bytes copied per iter via 4 word-loads + 4 word-stores (no shift).
     Composed Triple in `RComp R_h1 R_h2` form (5+6 chunk split).


===============================================================================
B15..B18  aligned tail (8 + 4)   —  Simple.lean, Block8.lean, BlockF.lean
===============================================================================
  ─────── B15 ─── 0x00200a4c → beq @ 0x200a50
  0x200a4c:  00867593   andi  a1, a2, 8        ; a1 := n & 8
  0x200a50:  00058e63   beq   a1, zero, +28    ; → 0x200a6c if no 8 left

  ─────── B16  block_8byte (Hoare/Block8.lean) ─── 0x00200a54..0x00200a68 ───
  0x200a54:  00072583   lw    a1, 0(a4)
  0x200a58:  00472783   lw    a5, 4(a4)        ; 2 word-loads
  0x200a5c:  00b6a023   sw    a1, 0(a3)
  0x200a60:  00f6a223   sw    a5, 4(a3)        ; 2 word-stores
  0x200a64:  00868693   addi  a3, a3, 8        ; dst += 8
  0x200a68:  00870713   addi  a4, a4, 8        ; src += 8

  R_block_8byte: copies 8 bytes (= mem[src..src+7] → mem[dst..dst+7]);
                 dst, src each += 8; falls through to B17.

  ─────── B17 ─── 0x00200a6c → beq @ 0x200a70
  0x200a6c:  00467593   andi  a1, a2, 4        ; a1 := n & 4
  0x200a70:  16058263   beq   a1, zero, +356   ; → 0x200bd4 if no 4 left

  ─────── B18  block_4byte (Hoare/BlockF.lean) ─── 0x00200a74..0x00200a84 ───
  0x200a74:  00072583   lw    a1, 0(a4)
  0x200a78:  00b6a023   sw    a1, 0(a3)
  0x200a7c:  00468693   addi  a3, a3, 4        ; dst += 4
  0x200a80:  00470713   addi  a4, a4, 4        ; src += 4
  0x200a84:  1500006f   jal   zero, +336       ; → 0x200bd4 (B29 byte tail)

  R_block_4byte: copies 4 bytes (= mem[src..src+3] → mem[dst..dst+3]);
                 dst, src each += 4; pc → 0x200bd4.


===============================================================================
B19  block_F_unaligned2_setup   —  Hoare/Blocks/Setups.lean
PCs 0x00200a88..0x00200a9c  (6 instr).
First-iteration preamble for dst-align=3 word-loop (16-byte chunks, shift=8).
===============================================================================
  0x200a88:  00072783   lw    a5, 0(a4)
  0x200a8c:  00168593   addi  a1, a3, 1
  0x200a90:  00f68023   sb    a5, 0(a3)        ; *(dst+0) := lo8(a5)
  0x200a94:  fff60613   addi  a2, a2, -1       ; n -= 1
  0x200a98:  01070693   addi  a3, a4, 16       ; a3 := src+16
  0x200a9c:  01200713   addi  a4, zero, 18     ; a4 := 18 (loop threshold)

  R: writes 1 src byte to dst; a3 ← src+16, a4 ← 18, n -= 1.


===============================================================================
B20  block_F_unaligned2   —  Hoare/Blocks/UnalignedBody.lean
PCs 0x00200aa0..0x00200afc  (24 instr).  = `mk_block_F_unaligned 8 24`.
Same 16-byte unaligned-loop body as B9, shifted differently.
===============================================================================
  0x200aa0:  ff46a803   lw    a6, -12(a3)
  0x200aa4:  0087d793   srli  a5, a5, 8
  0x200aa8:  01881893   slli  a7, a6, 24
  0x200aac:  ff86a283   lw    t0, -8(a3)
  0x200ab0:  00f8e7b3   or    a5, a7, a5
  0x200ab4:  00f5a023   sw    a5, 0(a1)
  0x200ab8:  00885793   srli  a5, a6, 8
  0x200abc:  01829813   slli  a6, t0, 24
  0x200ac0:  ffc6a883   lw    a7, -4(a3)
  0x200ac4:  00f867b3   or    a5, a6, a5
  0x200ac8:  00f5a223   sw    a5, 4(a1)
  0x200acc:  0082d813   srli  a6, t0, 8
  0x200ad0:  01889293   slli  t0, a7, 24
  0x200ad4:  0006a783   lw    a5, 0(a3)
  0x200ad8:  0102e833   or    a6, t0, a6
  0x200adc:  0105a423   sw    a6, 8(a1)
  0x200ae0:  0088d813   srli  a6, a7, 8
  0x200ae4:  01879893   slli  a7, a5, 24
  0x200ae8:  0108e833   or    a6, a7, a6
  0x200aec:  0105a623   sw    a6, 12(a1)
  0x200af0:  01058593   addi  a1, a1, 16
  0x200af4:  ff060613   addi  a2, a2, -16
  0x200af8:  01068693   addi  a3, a3, 16
  0x200afc:  fac762e3   bltu  a4, a2, -92      ; → 0x200aa0 (loop back)


===============================================================================
B21  block_B21   —  Hoare/Blocks/Simple.lean
PCs 0x00200b00..0x00200b04  (2 instr).
===============================================================================
  0x200b00:  ff168713   addi  a4, a3, -15      ; a4 := a3 - 15
  0x200b04:  0880006f   jal   zero, +136       ; → 0x200b8c (B25 tail dispatch)


===============================================================================
B22  block_F_unaligned3_setup   —  Hoare/Blocks/Setups.lean
PCs 0x00200b08..0x00200b24  (8 instr).
First-iteration preamble for dst-align=2 word-loop (shift=16).
===============================================================================
  0x200b08:  00072783   lw    a5, 0(a4)
  0x200b0c:  00f68023   sb    a5, 0(a3)        ; *(dst+0) := lo8(a5)
  0x200b10:  0087d813   srli  a6, a5, 8
  0x200b14:  00268593   addi  a1, a3, 2
  0x200b18:  010680a3   sb    a6, 1(a3)        ; *(dst+1) := lo8(a6)
  0x200b1c:  ffe60613   addi  a2, a2, -2       ; n -= 2
  0x200b20:  01070693   addi  a3, a4, 16
  0x200b24:  01100713   addi  a4, zero, 17     ; a4 := 17


===============================================================================
B23  block_F_unaligned3   —  Hoare/Blocks/UnalignedBody.lean
PCs 0x00200b28..0x00200b84  (24 instr).  = `mk_block_F_unaligned 16 16`.
===============================================================================
  0x200b28:  ff46a803   lw    a6, -12(a3)
  0x200b2c:  0107d793   srli  a5, a5, 16
  0x200b30:  01081893   slli  a7, a6, 16
  0x200b34:  ff86a283   lw    t0, -8(a3)
  0x200b38:  00f8e7b3   or    a5, a7, a5
  0x200b3c:  00f5a023   sw    a5, 0(a1)
  0x200b40:  01085793   srli  a5, a6, 16
  0x200b44:  01029813   slli  a6, t0, 16
  0x200b48:  ffc6a883   lw    a7, -4(a3)
  0x200b4c:  00f867b3   or    a5, a6, a5
  0x200b50:  00f5a223   sw    a5, 4(a1)
  0x200b54:  0102d813   srli  a6, t0, 16
  0x200b58:  01089293   slli  t0, a7, 16
  0x200b5c:  0006a783   lw    a5, 0(a3)
  0x200b60:  0102e833   or    a6, t0, a6
  0x200b64:  0105a423   sw    a6, 8(a1)
  0x200b68:  0108d813   srli  a6, a7, 16
  0x200b6c:  01079893   slli  a7, a5, 16
  0x200b70:  0108e833   or    a6, a7, a6
  0x200b74:  0105a623   sw    a6, 12(a1)
  0x200b78:  01058593   addi  a1, a1, 16
  0x200b7c:  ff060613   addi  a2, a2, -16
  0x200b80:  01068693   addi  a3, a3, 16
  0x200b84:  fac762e3   bltu  a4, a2, -92      ; → 0x200b28 (loop back)


===============================================================================
B24  block_B24   —  Hoare/Blocks/Simple.lean
PCs 0x00200b88  (1 instr — falls through to B25)
===============================================================================
  0x200b88:  ff268713   addi  a4, a3, -14      ; a4 := a3 - 14


===============================================================================
B25..B27  final tail dispatch   —  Hoare/Blocks/Simple.lean
After all 16-byte loops converge: how many bytes remain?  Dispatch to
1/2/4/8/16-byte byte-by-byte tail copies.
===============================================================================
  ─────── B25 ─── 0x00200b8c..0x00200b94 → bne @ 0x200b94
  0x200b8c:  00058693   addi  a3, a1, 0        ; a3 := a1  (dst+i)
  0x200b90:  01067593   andi  a1, a2, 16       ; a1 := n & 16
  0x200b94:  08059263   bne   a1, zero, +132   ; → 0x200c18 (B36 16-byte tail)

  ─────── B26 ─── 0x00200b98..0x00200b9c → bne @ 0x200b9c
  0x200b98:  00867593   andi  a1, a2, 8        ; a1 := n & 8
  0x200b9c:  10059863   bne   a1, zero, +272   ; → 0x200cac (B38 8-byte tail)

  ─────── B27 ─── 0x00200ba0..0x00200ba4 → beq @ 0x200ba4
  0x200ba0:  00467593   andi  a1, a2, 4        ; a1 := n & 4
  0x200ba4:  02058863   beq   a1, zero, +48    ; → 0x200bd4 (B29 if no 4 left)


===============================================================================
B28  block_4byte_unaligned   —  Hoare/Blocks/Tail4Unaligned.lean
PCs 0x00200ba8..0x00200bd0  (11 instr).  Byte-by-byte 4-byte copy.
===============================================================================
  0x200ba8:  00070583   lb    a1, 0(a4)
  0x200bac:  00170783   lb    a5, 1(a4)
  0x200bb0:  00270803   lb    a6, 2(a4)
  0x200bb4:  00b68023   sb    a1, 0(a3)
  0x200bb8:  00f680a3   sb    a5, 1(a3)
  0x200bbc:  00370583   lb    a1, 3(a4)
  0x200bc0:  01068123   sb    a6, 2(a3)
  0x200bc4:  00470713   addi  a4, a4, 4        ; src += 4
  0x200bc8:  00468793   addi  a5, a3, 4        ; a5  := dst+4
  0x200bcc:  00b681a3   sb    a1, 3(a3)
  0x200bd0:  00078693   addi  a3, a5, 0        ; a3 := dst+4
  Triple R: 4 bytes copied (via 4×lb / 4×sb interleave); dst, src each += 4.


===============================================================================
B29..B31  1- and 2-byte tail dispatch  —  Hoare/Blocks/Simple.lean
===============================================================================
  ─────── B29 ─── 0x00200bd4..0x00200bd8 → bne @ 0x200bd8
  0x200bd4:  00267593   andi  a1, a2, 2
  0x200bd8:  00059863   bne   a1, zero, +16    ; → 0x200be8 (B32) if 2 left

  ─────── B30 ─── 0x00200bdc..0x00200be0 → bne @ 0x200be0
  0x200bdc:  00167593   andi  a1, a2, 1
  0x200be0:  02059663   bne   a1, zero, +44    ; → 0x200c0c (B34) if 1 left

  ─────── B31  block_ret ─── 0x00200be4 ─────────────────────────────────
  0x200be4:  00008067   jalr  zero, 0(ra)      ; return


===============================================================================
B32  block_2byte_tail   —  Hoare/Blocks/Tail2.lean
PCs 0x00200be8..0x00200c00  (6 instr).
===============================================================================
  0x200be8:  00070583   lb    a1, 0(a4)
  0x200bec:  00170783   lb    a5, 1(a4)
  0x200bf0:  00b68023   sb    a1, 0(a3)
  0x200bf4:  00270713   addi  a4, a4, 2
  0x200bf8:  00268593   addi  a1, a3, 2
  0x200bfc:  00f680a3   sb    a5, 1(a3)
  0x200c00:  00058693   addi  a3, a1, 0        ; a3 := dst+2

  R_block_2byte_tail: 2 bytes copied (mem[src..src+1] → mem[dst..dst+1]);
                      dst, src each += 2.


===============================================================================
B33..B35  1-byte dispatch + tail  —  Hoare/Blocks/{Simple,Tail1}.lean
===============================================================================
  ─────── B33 ─── 0x00200c04..0x00200c08 → beq @ 0x200c08
  0x200c04:  00167593   andi  a1, a2, 1
  0x200c08:  fc058ee3   beq   a1, zero, -36    ; → 0x200be4 (B31 ret) if no byte

  ─────── B34  block_1byte_tail (Tail1.lean) ─── 0x00200c0c..0x00200c10 ───
  0x200c0c:  00070583   lb    a1, 0(a4)        ; load 1 byte
  0x200c10:  00b68023   sb    a1, 0(a3)        ; store 1 byte
  R_block_1byte_tail: 1 byte copied (mem[src] → mem[dst]).

  ─────── B35  block_ret ─── 0x00200c14 ─────────────────────────────────
  0x200c14:  00008067   jalr  zero, 0(ra)      ; return


===============================================================================
B36  block_16byte_unaligned   —  Hoare/Blocks/Tail16Unaligned.lean
PCs 0x00200c18..0x00200c9c  (34 instr).  Byte-by-byte 16-byte copy (no loop).
Split into two halves (h1/h2 of 17 instr each); SP-form Triple.
===============================================================================
  0x200c18:  00070583   lb    a1, 0(a4)
  0x200c1c:  00170783   lb    a5, 1(a4)
  0x200c20:  00270803   lb    a6, 2(a4)
  0x200c24:  00b68023   sb    a1, 0(a3)
  0x200c28:  00f680a3   sb    a5, 1(a3)
  0x200c2c:  00370583   lb    a1, 3(a4)
  0x200c30:  01068123   sb    a6, 2(a3)
  0x200c34:  00470783   lb    a5, 4(a4)
  0x200c38:  00570803   lb    a6, 5(a4)
  0x200c3c:  00b681a3   sb    a1, 3(a3)
  0x200c40:  00670583   lb    a1, 6(a4)
  0x200c44:  00f68223   sb    a5, 4(a3)
  0x200c48:  010682a3   sb    a6, 5(a3)
  0x200c4c:  00770783   lb    a5, 7(a4)
  0x200c50:  00b68323   sb    a1, 6(a3)
  0x200c54:  00870583   lb    a1, 8(a4)
  0x200c58:  00970803   lb    a6, 9(a4)
  -- h1 ends ↑ ; h2 begins ↓
  0x200c5c:  00f683a3   sb    a5, 7(a3)
  0x200c60:  00a70783   lb    a5, 10(a4)
  0x200c64:  00b68423   sb    a1, 8(a3)
  0x200c68:  010684a3   sb    a6, 9(a3)
  0x200c6c:  00b70583   lb    a1, 11(a4)
  0x200c70:  00f68523   sb    a5, 10(a3)
  0x200c74:  00c70783   lb    a5, 12(a4)
  0x200c78:  00d70803   lb    a6, 13(a4)
  0x200c7c:  00b685a3   sb    a1, 11(a3)
  0x200c80:  00e70583   lb    a1, 14(a4)
  0x200c84:  00f68623   sb    a5, 12(a3)
  0x200c88:  010686a3   sb    a6, 13(a3)
  0x200c8c:  00f70783   lb    a5, 15(a4)
  0x200c90:  00b68723   sb    a1, 14(a3)
  0x200c94:  01070713   addi  a4, a4, 16
  0x200c98:  01068593   addi  a1, a3, 16
  0x200c9c:  00f687a3   sb    a5, 15(a3)

  R: 16 bytes copied byte-by-byte; src, dst each += 16; SP form.


===============================================================================
B37  block_B37   —  Hoare/Blocks/Simple.lean
PCs 0x00200ca0..0x00200ca8  (3 instr, beq terminator).
===============================================================================
  0x200ca0:  00058693   addi  a3, a1, 0
  0x200ca4:  00867593   andi  a1, a2, 8
  0x200ca8:  ee058ce3   beq   a1, zero, -264   ; → 0x200ba0 (back to B27) if no 8


===============================================================================
B38  block_8byte_unaligned   —  Hoare/Blocks/Tail8Unaligned.lean
PCs 0x00200cac..0x00200cf0  (18 instr).  Byte-by-byte 8-byte copy.
===============================================================================
  0x200cac:  00070583   lb    a1, 0(a4)
  0x200cb0:  00170783   lb    a5, 1(a4)
  0x200cb4:  00270803   lb    a6, 2(a4)
  0x200cb8:  00b68023   sb    a1, 0(a3)
  0x200cbc:  00f680a3   sb    a5, 1(a3)
  0x200cc0:  00370583   lb    a1, 3(a4)
  0x200cc4:  01068123   sb    a6, 2(a3)
  0x200cc8:  00470783   lb    a5, 4(a4)
  0x200ccc:  00570803   lb    a6, 5(a4)
  0x200cd0:  00b681a3   sb    a1, 3(a3)
  0x200cd4:  00670583   lb    a1, 6(a4)
  0x200cd8:  00f68223   sb    a5, 4(a3)
  0x200cdc:  010682a3   sb    a6, 5(a3)
  0x200ce0:  00770783   lb    a5, 7(a4)
  0x200ce4:  00b68323   sb    a1, 6(a3)
  0x200ce8:  00870713   addi  a4, a4, 8
  0x200cec:  00868593   addi  a1, a3, 8
  0x200cf0:  00f683a3   sb    a5, 7(a3)

  R: 8 bytes copied byte-by-byte; src, dst each += 8; SP form.


===============================================================================
B39..B40  4-byte / loop back   —  Hoare/Blocks/Simple.lean
===============================================================================
  ─────── B39 ─── 0x00200cf4..0x00200cfc → bne @ 0x200cfc
  0x200cf4:  00058693   addi  a3, a1, 0
  0x200cf8:  00467593   andi  a1, a2, 4
  0x200cfc:  ea0596e3   bne   a1, zero, -340   ; → 0x200ba8 (B28) if 4 left

  ─────── B40 ─── 0x00200d00 ─────────────────────────────────────────────
  0x200d00:  ed5ff06f   jal   zero, -300       ; → 0x200bd4 (B29 ret dispatch)


===============================================================================
Summary
===============================================================================
- 40 basic blocks, all proved (`Triple block_BN R_BN` for each N).
- 5 main "control regions":
    Prologue:     B1  (alignment check)
    Byte prefix:  B2  (loop body) — full loop in LoopBytePrefix.lean
    Word loops:   B8/9, B11/12, B13/14, B19/20, B22/23 (4 aligned/unaligned)
    Aligned tails:        B15/16/17/18  (8 + 4)
    Final dispatch+tails: B25/26/27/28/29/30/31/32/33/34/35/36/37/38/39/40

- Outstanding: composing the per-block triples into a full memcpy correctness
  theorem (the CFG-layer work).  Currently:
    * loop_byte_prefix_full_correct (LoopBytePrefix.lean): K=1 case PROVED,
      K=2,3 cases sorry'd (analogous structure).
    * All other blocks: standalone triples only; no CFG composition yet.
