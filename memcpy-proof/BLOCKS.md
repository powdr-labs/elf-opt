# memcpy basic-block tracker

Every block is a maximal straight-line region of `memcpy.elf` ending at
either a control-flow instruction (`b*`, `jal`, `jalr`) or just before a
branch target.  Tick `[x]` once a `Triple` proof exists in
`MemcpyProof/Hoare/`.

## Status summary

- **Total blocks:** 40
- **Done:** 37 — including the byte-prefix loop body (B2, 14 instr, 3-chunk split).
- **Remaining:** 3 — B36 (16-byte unaligned tail, ~34 instr), B38 (8-byte unaligned tail, ~18 instr), plus B14's structured R (currently in composed form).

> **Refactor note (2026-06-02):** the `halted` / `haltAt` State fields were removed.  Hoare-level proofs no longer carry a halted precondition; the "routine has returned" predicate moves to the CFG/harness layer as `s.pc = retSentinel`.  All existing block proofs were updated; the foundation now lives in 3 files (Block.lean, Triple.lean, InstrTriples.lean) with no halted bookkeeping.

## Branch / jump targets (entry points)

Targets reachable by branches/jumps, computed from the assembly:

```
0x002008f8   function entry
0x00200914   target of bne at 0x200944 (byte-prefix loop back)
0x00200998   target of bltu at 0x2009f4 (unaligned-by-1 loop back)
0x00200a00   target of bne at 0x200908
0x00200a10   target of beq at 0x20094c
0x00200a1c   target of bltu at 0x200a48 (aligned 16-byte loop back)
0x00200a4c   target of bltu at 0x200a14
0x00200a6c   target of beq at 0x200a50
0x00200a88   target of beq at 0x20095c
0x00200aa0   target of bltu at 0x200afc (unaligned-by-2 loop back)
0x00200b08   target of beq at 0x200964
0x00200b28   target of bltu at 0x200b84 (unaligned-by-3 loop back)
0x00200b8c   target of jal at 0x2009fc / 0x200b04 / 0x200d00
0x00200b90   target of bltu at 0x200954 / bne at 0x20096c (post-prefix)
0x00200ba0   target of beq at 0x200ca8
0x00200ba8   target of bne at 0x200cfc
0x00200bd4   target of beq at 0x200a70 / 0x200ba4 / jal at 0x200a84
0x00200be4   target of beq at 0x200c08 (return)
0x00200be8   target of bne at 0x200bd8
0x00200c0c   target of bne at 0x200be0
0x00200c18   target of bne at 0x200b94
0x00200cac   target of bne at 0x200b9c
```

## Basic blocks (in PC order)

### Function prologue

- [x] **B1 `block_align_check`** — 0x2008f8..0x200904 (4 instr) → bne @0x200908
  ```
  andi a3,a1,3 ; sltiu a3,a3,1 ; sltiu a4,a2,1 ; or a3,a3,a4
  ```
  *Computes `(src aligned) ∨ (n = 0)`; bne dispatches to fast path or byte-prefix loop.*

### Byte-prefix loop (aligns src by copying bytes 1-at-a-time)

- [x] **B2 `block_byte_prefix_body`** *(Blocks/BytePrefix.lean)* — 0x20090c..0x200940 (14 instr) → bne @0x200944
  *First-iteration preamble fused with loop body. Uses lb/sb/andi/sltu/and/addi×many. Split into 5+5+4 chunks; the inner `Triple` is in composed (`RComp R_c1 (RComp R_c2 R_c3)`) form. Builds in ~0.4s.*

### Alignment dispatch (after byte-prefix loop completes)

- [x] **B3 `block_B3`** *(Blocks/Simple.lean)* — 0x200948..0x200948 (1 instr) → beq @0x20094c
  *`andi a1,a3,3` — recompute dst align; beq jumps to aligned-fast-path setup if 0.*

- [x] **B4 `block_B4`** *(Blocks/Simple.lean)* — 0x200950..0x200950 (1 instr) → bltu @0x200954
  *`addi a5,zero,32` — bltu to byte-fallback if n<32.*

- [x] **B5 `block_B5`** *(Blocks/Simple.lean)* — 0x200958..0x200958 (1 instr) → beq @0x20095c
  *`addi a5,zero,3` — dispatch to align-3 case.*

- [x] **B6 `block_B6`** *(Blocks/Simple.lean)* — 0x200960..0x200960 (1 instr) → beq @0x200964
  *`addi a5,zero,2` — dispatch to align-2 case.*

- [x] **B7 `block_B7`** *(Blocks/Simple.lean)* — 0x200968..0x200968 (1 instr) → bne @0x20096c
  *`addi a5,zero,1` — bne to byte-fallback if not align-1.*

### Unaligned-by-1 16-byte loop (when dst-align is 1)

- [x] **B8 `block_F_unaligned1_setup`** *(Blocks/Setups.lean)* — 0x200970..0x200994 (10 instr)
  *First-iteration preamble: lw/sb/srli/sb/srli/addi/sb/addi/addi/addi.*

- [x] **B9 `block_F_unaligned1`** *(Blocks/UnalignedBody.lean)* — 0x200998..0x2009f0 (23 instr) → bltu @0x2009f4
  *Proved via parametric `mk_block_F_unaligned 24 8` split into 5 chunks (6/5/5/4/3); each chunk has its own clean structured R; the block triple is the .append composition.*

- [x] **B10 `block_B10`** *(Blocks/Simple.lean)* — 0x2009f8..0x2009f8 (1 instr) → jal @0x2009fc
  *`addi a4,a3,-13` then unconditional jump to 0x200b8c (the final tail dispatch).*

### Setup before alignment-fast-path

- [x] **B11 `block_setup_align`** *(Blocks/Setups.lean)* — 0x200a00..0x200a08 (3 instr) → bne @0x200a0c
  *`addi a3,a0,0 ; addi a4,a1,0 ; andi a1,a3,3` — copy dst/src into working regs and compute dst align.*

- [x] **B12 `block_B12`** *(Blocks/Simple.lean)* — 0x200a10..0x200a10 (1 instr) → bltu @0x200a14
  *`addi a1,zero,16` — bltu to tail path if n<16.*

### Aligned 16-byte loop (the main fast path)

- [x] **B13 `block_F_first`** *(Blocks/AlignedLoop.lean)* — 0x200a18..0x200a44 (12 instr) → bltu @0x200a48
  *First iteration: preamble + B14.  Triple given in composed (RComp) form.*

- [x] **B14 `block_F_iter`** *(Blocks/AlignedLoop.lean)* — 0x200a1c..0x200a44 (11 instr) → bltu @0x200a48
  *Pure loop body, split into 5+6 half-chunks for typecheck speed; Triple in composed (RComp R_h1 R_h2) form.*

### Aligned tails

- [x] **B15 `block_B15`** *(Blocks/Simple.lean)* — 0x200a4c..0x200a4c (1 instr) → beq @0x200a50
  *`andi a1,a2,8` — check if 8 more bytes remain.*

- [x] **B16 `block_8byte`** — 0x200a54..0x200a68 (6 instr)
  *2 lw / 2 sw / 2 addi, copies 8 bytes.  Falls through to B17.*

- [x] **B17 `block_B17`** *(Blocks/Simple.lean)* — 0x200a6c..0x200a6c (1 instr) → beq @0x200a70
  *`andi a1,a2,4` — check if 4 more bytes remain.*

- [x] **B18 `block_4byte`** — 0x200a74..0x200a80 (4 instr) → jal @0x200a84
  *lw, sw, 2 addi.  Then unconditional jump to 0x200bd4 (2/1-byte tail check).*

### Unaligned-by-2 16-byte loop

- [x] **B19 `block_F_unaligned2_setup`** *(Blocks/Setups.lean)* — 0x200a88..0x200a9c (6 instr)
  *First-iteration preamble.*

- [x] **B20 `block_F_unaligned2`** *(Blocks/UnalignedBody.lean)* — 0x200aa0..0x200af8 (23 instr) → bltu @0x200afc
  *= `mk_block_F_unaligned 8 24`.  Same parametric proof as B9.*

- [x] **B21 `block_B21`** *(Blocks/Simple.lean)* — 0x200b00..0x200b00 (1 instr) → jal @0x200b04
  *`addi a4,a3,-15` then jump to 0x200b8c.*

### Unaligned-by-3 16-byte loop

- [x] **B22 `block_F_unaligned3_setup`** *(Blocks/Setups.lean)* — 0x200b08..0x200b24 (8 instr)
  *First-iteration preamble.*

- [x] **B23 `block_F_unaligned3`** *(Blocks/UnalignedBody.lean)* — 0x200b28..0x200b80 (23 instr) → bltu @0x200b84
  *= `mk_block_F_unaligned 16 16`.  Same parametric proof as B9.*

- [x] **B24 `block_B24`** *(Blocks/Simple.lean)* — 0x200b88..0x200b88 (1 instr)
  *`addi a4,a3,-14` then falls through to B25.*

### Final tail dispatch (after all unaligned-16-byte loops converge here)

- [x] **B25 `block_B25`** *(Blocks/Simple.lean)* — 0x200b8c..0x200b90 (2 instr) → bne @0x200b94
  *`addi a3,a1,0 ; andi a1,a2,16` — check if 16 more bytes remain.*

- [x] **B26 `block_B26`** *(Blocks/Simple.lean)* — 0x200b98..0x200b98 (1 instr) → bne @0x200b9c
  *`andi a1,a2,8` — check if 8 more bytes remain.*

- [x] **B27 `block_B27`** *(Blocks/Simple.lean)* — 0x200ba0..0x200ba0 (1 instr) → beq @0x200ba4
  *`andi a1,a2,4` — check if 4 more bytes remain.*

### Byte-by-byte tails (used when dst was misaligned)

- [x] **B28 `block_4byte_unaligned`** *(Blocks/Tail4Unaligned.lean)* — 0x200ba8..0x200bd0 (11 instr)
  *4 lb / 4 sb / addi/addi/addi sequence — byte-by-byte 4-byte copy.  Split into 5+6 half-chunks; Triple in composed (RComp R_h1 R_h2) form.*

- [x] **B29 `block_B29`** *(Blocks/Simple.lean)* — 0x200bd4..0x200bd4 (1 instr) → bne @0x200bd8
  *`andi a1,a2,2` — check if 2 bytes remain.*

- [x] **B30 `block_B30`** *(Blocks/Simple.lean)* — 0x200bdc..0x200bdc (1 instr) → bne @0x200be0
  *`andi a1,a2,1` — check if 1 byte remains.*

- [x] **B31 `block_ret`** *(Blocks/Simple.lean)* — 0x200be4..0x200be4 (1 instr)
  *`jalr zero,0(ra)` — return when no bytes remain.  (Triple shared with B35.)*

- [x] **B32 `block_2byte_tail`** *(Blocks/Tail2.lean)* — 0x200be8..0x200c00 (6 instr)
  *2 lb / 2 sb / 2 addi — byte-by-byte 2-byte copy.  Falls through to B33.*

- [x] **B33 `block_B33`** *(Blocks/Simple.lean)* — 0x200c04..0x200c04 (1 instr) → beq @0x200c08
  *`andi a1,a2,1` — beq back to B31 if no byte remains.*

- [x] **B34 `block_1byte_tail`** *(Blocks/Tail1.lean)* — 0x200c0c..0x200c10 (2 instr)
  *lb + sb — byte-by-byte 1-byte copy.  Falls through to B35.*

- [x] **B35 `block_ret`** *(Blocks/Simple.lean — shared with B31)* — 0x200c14..0x200c14 (1 instr)
  *`jalr zero,0(ra)` — second return point.*

### Big unaligned tails (loop-free, byte-by-byte)

- [ ] **B36 `block_16byte_unaligned`** — 0x200c18..0x200c9c (~34 instr)
  *Copy 16 bytes one at a time via lb/sb sequence.  Falls through to B37.*

- [x] **B37 `block_B37`** *(Blocks/Simple.lean)* — 0x200ca0..0x200ca4 (2 instr) → beq @0x200ca8
  *`addi a3,a1,0 ; andi a1,a2,8` — check if 8 more bytes.*

- [ ] **B38 `block_8byte_unaligned`** — 0x200cac..0x200cf0 (~18 instr)
  *Copy 8 bytes one at a time via lb/sb sequence.  Falls through to B39.*

- [x] **B39 `block_B39`** *(Blocks/Simple.lean)* — 0x200cf4..0x200cf8 (2 instr) → bne @0x200cfc
  *`addi a3,a1,0 ; andi a1,a2,4` — bne back to B28 if 4 more bytes.*

- [x] **B40 `block_B40`** *(Blocks/Simple.lean)* — 0x200d00..0x200d00 (1 instr)
  *`jal zero,-300` — jumps unconditionally to 0x200bd4 (B29 entry).*

## Per-instruction-class Triple coverage

These are the `Triple_<class>` lemmas in `Hoare/InstrTriples.lean`:

- [x] `Triple_addi`, `Triple_andi`, `Triple_ori`
- [x] `Triple_slli`, `Triple_srli`
- [x] `Triple_sltiu`, `Triple_sltu`
- [x] `Triple_and`, `Triple_or`
- [x] `Triple_lw`, `Triple_sw`, `Triple_sb`, `Triple_lb`
- [x] `Triple_jal` (covers B10/B21/B24 1-instr blocks via per-block instantiation; B40 too)
- [x] `Triple_jalr` (covers B31/B35 returns)
- [ ] **Branch triples** (taken / not-taken variants for `bne`, `beq`, `bltu`).  Probably need a `BranchDelta` re-introduction or per-branch lemmas at the block-CFG composition level rather than here.

## Recommended next session

1. ~~Knock out the simple "single-instruction + branch" blocks (B3–B7, B12, B15, B17, B25–B27, B29–B30, B33, B37, B39).~~ ✅ done.

2. ~~Add `Triple_lb` and tackle the small tail blocks: B32 (2-byte), B34 (1-byte).~~ ✅ done.

3. Add `Triple_jal_zero` / `Triple_ret` and the return-path blocks B10, B18 (already proved sans the `jal`), B21, B31, B35, B40.

4. Tackle the big straight-line tails: B28 (11 instr lb/sb), B36 (16-byte byte-by-byte), B38 (8-byte byte-by-byte).

5. Tackle the unaligned-16-byte loop bodies (B8/B9, B19/B20, B22/B23) — these are the largest single blocks and exercise srli/slli/or for byte-stitching.

6. Misc small blocks remaining: B2 (byte-prefix loop body, 13 instr), B11 (setup_align, 3 instr), B13/B14 (aligned 16-byte loop), B24 (unaligned3 tail).

7. Once block-level coverage is complete, build the CFG layer that composes blocks based on branch outcomes, then prove loop invariants for the 4 copy loops.
