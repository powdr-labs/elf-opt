memcpy CFG — block-to-block jumps
==================================

40 basic blocks.  Two return points (B31 @ 0x200be4 and B35 @ 0x200c14).
Diagram conventions: `─►` = fall-through, `══►` = explicit branch/jump.


High-level overview
-------------------

                          ┌──────────────┐
                          │ entry 0x2008f8│
                          └──────┬───────┘
                                 │
                                 ▼
                        ┌─────────────────┐
                        │  B1 align-check │
                        └─┬──────────────┬┘
              src aligned │              │ src misaligned
              OR n=0      │              │ (a1 & 3 ≠ 0 ∧ a2 ≠ 0)
                          │              │
                          │              ▼
                          │     ┌──────────────────┐
                          │     │ B2 byte-prefix   │
                          │     │   loop (1-3      │◄──┐
                          │     │    iterations)   │   │ bne back
                          │     └──────┬───────────┘   │ (each iter)
                          │            │ exits with     │
                          │            │ dst aligned    │
                          │            │ or n ≤ 0       │
                          │            ▼               │
                          │     ┌──────────────────┐   │
                          │     │  B3-B7 dispatch  │   │
                          │     │  (decide which   │   │
                          │     │   16-byte loop)  │   │
                          │     └─┬────┬────┬────┬─┘   │
                          │       │    │    │    │     │
                          │       │ a=1│ a=2│ a=3│ n<32│
                          │       │    │    │    │ or  │
                          │       │    │    │    │ else│
                          │       │    │    │    │     │
                          ▼       ▼    ▼    ▼    │     │
              ┌──────────────┐ ┌────┐ ┌────┐ ┌────┐    │
              │ B11 setup    │ │ B8 │ │B19 │ │B22 │    │
              │   align      │ │ +  │ │ +  │ │ +  │    │
              └──────┬───────┘ │ B9 │ │B20 │ │B23 │    │
                     │ bne back to B3       │  (each   │
                     │ (recheck align)      │  with    │
                     │                      │  16-byte │
                     │ aligned!             │  loop)   │
                     ▼                      │          │
              ┌──────────────┐              │          │
              │ B12 n < 16 ? │              │          │
              └─┬───────────┬┘              │          │
                │           │ n < 16        │          │
                │           ▼               ▼          │
                │ n ≥ 16 ┌──────┐    ┌─────────────┐  │
                │        │ B15  │◄───┤ B10/B21/B24 │  │
                │        │ tail │    │ (epilogues) │  │
                │        │ chain│    └──────┬──────┘  │
                │        └──┬───┘           │         │
                │           │               ▼         │
                ▼           │      ┌──────────────────┴┐
       ┌────────────────┐   │      │ B25 final tail    │◄──── n < 32 path
       │ B13/B14 aligned│   │      │   dispatch        │
       │   16-byte loop │   │      │   (1/2/4/8/16)    │
       │   ◄────loops───┤   │      └────────┬──────────┘
       └────────┬───────┘   │               │
                │           │               ▼
                ▼           │      ┌────────────────────┐
       ┌────────────────────┘      │ B29..B35 1/2-byte  │
       │ B15-B18 aligned tail      │  tail + return     │
       │  (8/4 bytes)              └────────┬───────────┘
       └────────────┬──────────────┐        │
                    │              │        ▼
                    ▼              │   ┌─────────┐
              ┌────────┐           │   │ jalr ra │
              │  B29   │◄──────────┘   │ (return)│
              │ tail   │               └─────────┘
              │ chain  │
              └────────┘


Per-region detail
-----------------

(1) Prologue + byte-prefix loop + dispatch
   PCs 0x2008f8..0x20096c

       0x2008f8 B1 ─── bne a3,0 (aligned OR n=0?) ═══════════╗
       0x20090c B2 byte-prefix-loop body                     ║
                   │     ▲                                   ║
                   │ bne │ (loop continues)                  ║
                   │ ────┘ target 0x200914                   ║
                   ▼ (a7=0, loop exits)                      ║
       0x200948 B3 ─── beq a1,0 (dst aligned?) ══════╗       ║
                   ▼ no                              ║       ║
       0x200950 B4 ─── bltu a2<32? (small n) ══╗     ║       ║
                   ▼ no                        ║     ║       ║
       0x200958 B5 ─── beq a1,3 (align-3?) ═╗  ║     ║       ║
                   ▼ no                     ║  ║     ║       ║
       0x200960 B6 ─── beq a1,2 (align-2?)  ║  ║     ║       ║
                   ▼ no   │ yes             ║  ║     ║       ║
       0x200968 B7 ─── bne a1≠1 ══╗  │      ║  ║     ║       ║
                   ▼ no           ║  │      ║  ║     ║       ║
                  B8 (unalign-1)  ║  │      ║  ║     ║       ║
                   │              ║  │      ║  ║     ║       ║
       ╔═══════════╝              ║  │      ║  ║     ║       ║
       ║ target 0x200b90 (into B25)║  │      ║  ║     ║       ║
       ║                          ║  │      ║  ║     ║       ║
       ║ target 0x200a88 (B19)════╝  │      ║  ║     ║       ║
       ║                             │      ║  ║     ║       ║
       ║ target 0x200b08 (B22)═══════╝      ║  ║     ║       ║
       ║                                    ║  ║     ║       ║
       ║ target 0x200b90 (into B25)═════════╝  ║     ║       ║
       ║                                       ║     ║       ║
       ║ target 0x200a10 (B12)═════════════════╝     ║       ║
       ║                                             ║       ║
       ║ target 0x200b90 (into B25, n<32)════════════╝       ║
       ║                                                     ║
       ║ target 0x200a00 (B11)═══════════════════════════════╝


(2) Three unaligned 16-byte word-loops
   PCs 0x200970..0x200b88

       B8 (setup-1) ──► B9 (16-byte loop, dst-align=1)
                            │       ▲
                            │       │ bltu n>16
                            └───────┘ loop back
                            │ exit (n ≤ 16)
                            ▼
                       B10  addi a4,a3,-13
                            │
                            ║ jal +400 ═══► 0x200b8c (B25)

       B19 (setup-2) ──► B20 (loop, dst-align=3)
                            │       ▲
                            │       │ bltu n>16
                            └───────┘
                            ▼ exit
                       B21  addi a4,a3,-15
                            ║ jal +136 ═══► 0x200b8c (B25)

       B22 (setup-3) ──► B23 (loop, dst-align=2)
                            │       ▲
                            │       │ bltu n>16
                            └───────┘
                            ▼ exit
                       B24  addi a4,a3,-14 ──► B25 (fall through)


(3) Aligned fast path
   PCs 0x200a00..0x200a84

       B11 setup_align (a3,a4 = dst,src; a1 = dst & 3)
            │
            ║ bne a1≠0 ═══► 0x20094c (back to B3 dispatch)
            │
            ▼ (dst aligned, all good)
       B12 (n < 16?)
            │
            ║ bltu ═══► 0x200a4c (B15, tail chain)
            │
            ▼ (n ≥ 16)
       B13 preamble + B14 loop body
            │       ▲
            │       │ bltu n>15
            └───────┘
            ▼ exit
       B15 (n & 8 ?)
            │
            ║ beq a1=0 ═══► 0x200a6c (B17, skip 8)
            │
            ▼ (8 left)
       B16 copy 8 bytes (lw,lw,sw,sw,addi,addi)
            │
            ▼
       B17 (n & 4 ?)
            │
            ║ beq a1=0 ═══► 0x200bd4 (B29, skip 4)
            │
            ▼ (4 left)
       B18 copy 4 bytes
            │
            ║ jal +336 ═══► 0x200bd4 (B29)


(4) Final tail dispatch (after all unaligned-16 loops converge)
   PCs 0x200b8c..0x200ba4

                 ┌── from B10/B21 (jal) ──┐
                 │                        │
                 │     ┌── from B24 fall ─┤
                 ▼     ▼                  │
           ┌──────────────┐               │
           │ B25 (n & 16?)│               │
           └──────┬───────┘               │
                  │ bne ═══► 0x200c18 (B36 16-byte tail)
                  │
                  ▼ (no 16 left)
           ┌──────────────┐
           │ B26 (n & 8?) │
           └──────┬───────┘
                  │ bne ═══► 0x200cac (B38 8-byte tail)
                  │
                  ▼ (no 8 left)
           ┌──────────────┐ ◄── B37 beq back here
           │ B27 (n & 4?) │
           └──────┬───────┘
                  │ beq ═══► 0x200bd4 (B29 no 4)
                  │
                  ▼ (4 left)
           ┌──────────────┐
           │ B28 4-byte   │
           │ byte-by-byte │
           └──────┬───────┘
                  ▼
                 B29 (see region 5)

   Also: B36 ──► B37 ─── beq back to B27 ──► B38 ─── B39 ─── bne → B28
                                                            └── B40 → jal → B29


(5) 1/2-byte tail + returns
   PCs 0x200bd4..0x200c14

       ┌── from B17 beq, B18 jal, B27 beq, B40 jal, B28 fall ──┐
       ▼                                                       │
   ┌────────────────┐                                          │
   │ B29 (n & 2 ?)  │                                          │
   └───────┬────────┘                                          │
           │ bne ═══► 0x200be8 (B32 2-byte tail)               │
           │                                                   │
           ▼ (no 2 left)                                       │
   ┌────────────────┐                                          │
   │ B30 (n & 1 ?)  │                                          │
   └───────┬────────┘                                          │
           │ bne ═══► 0x200c0c (B34 1-byte tail)               │
           │                                                   │
           ▼ (no 1 left)                                       │
   ┌────────────────┐                                          │
   │ B31 jalr ret   │       ← exit                             │
   └────────────────┘                                          │
                                                               │
   ┌── from B29 bne ──► B32 (2-byte copy) ──► B33 (n & 1 ?) ───┘
   │
   │  B33 ── beq ═══► 0x200be4 (B31 ret, no 1 left)
   │       ── fall ──► B34 (1-byte copy) ──► B35 jalr ret  ← exit
   │
   └── from B30 bne ──► B34 ──► B35 ret


(6) Big byte-by-byte tails (16- and 8-byte unaligned)
   PCs 0x200c18..0x200d00

       B25 ── bne ═══► B36 (16-byte tail) ──► B37 (n & 8 ?)
                                                   │
                                                   ║ beq ═══► 0x200ba0 (back to B27)
                                                   ▼ (8 left)
       B26 ── bne ═══► B38 (8-byte tail)  ──► B39 (n & 4 ?)
                                                   │
                                                   ║ bne ═══► 0x200ba8 (B28)
                                                   ▼ (no 4)
                                              B40  jal ═══► 0x200bd4 (B29)


Branch targets summary (cross-references)
-----------------------------------------

  0x002008f8  function entry                            ← outer caller
  0x00200914  target of bne @ B2                        ← B2 self-loop
  0x00200998  target of bltu @ B9 end                   ← B9 self-loop
  0x00200a00  target of bne @ B1                        ← B1 → B11
  0x00200a10  target of beq @ B3                        ← B3 → B12
  0x00200a1c  target of bltu @ B14 end                  ← B14 self-loop
  0x00200a4c  target of bltu @ B12                      ← B12 → B15
  0x00200a6c  target of beq @ B15                       ← B15 → B17
  0x00200a88  target of beq @ B5                        ← B5 → B19
  0x00200aa0  target of bltu @ B20 end                  ← B20 self-loop
  0x00200b08  target of beq @ B6                        ← B6 → B22
  0x00200b28  target of bltu @ B23 end                  ← B23 self-loop
  0x00200b8c  target of jal @ B10, B21, B40             ← merge into B25
  0x00200b90  target of bltu @ B4, bne @ B7             ← skip into B25
  0x00200ba0  target of beq @ B37                       ← B37 → B27
  0x00200ba8  target of bne @ B39                       ← B39 → B28
  0x00200bd4  target of beq @ B17, B27 / jal @ B18, B40 ← merge into B29
  0x00200be4  target of beq @ B33                       ← B33 → B31 (ret)
  0x00200be8  target of bne @ B29                       ← B29 → B32
  0x00200c0c  target of bne @ B30                       ← B30 → B34
  0x00200c18  target of bne @ B25                       ← B25 → B36
  0x00200cac  target of bne @ B26                       ← B26 → B38


Loops (back-edges only)
-----------------------

  B2 ──► itself          byte-prefix      (1-3 iterations)
  B9 ──► itself          unaligned-by-1   (n ≥ 16 chunks)
  B14 ──► itself         aligned          (n ≥ 16 chunks)
  B20 ──► itself         unaligned-by-3   (n ≥ 16 chunks)
  B23 ──► itself         unaligned-by-2   (n ≥ 16 chunks)
  B11 ──► B3             align recheck (only if dst was unaligned)
  B33 ──► B31            (effectively a single-step merge into ret)
  B37 ──► B27            (after 16-byte tail, recheck 8/4)
  B39 ──► B28            (after 8-byte tail, recheck 4)
  B40 ──► B29            (after 8-byte tail, no 4, merge into 1/2 dispatch)


Joins (multiple incoming edges)
-------------------------------

  B12  ←  B11 fall, B3 beq
  B15  ←  B14 fall, B12 bltu
  B17  ←  B16 fall, B15 beq
  B25  ←  B24 fall, B10/B21 jal, B4/B7 bltu/bne
  B27  ←  B26 fall, B37 beq
  B28  ←  B27 fall, B39 bne
  B29  ←  B28 fall, B17/B27 beq, B18/B40 jal
  B31  ←  B30 fall, B33 beq           (return)
  B35  ←  B34 fall                    (return)
