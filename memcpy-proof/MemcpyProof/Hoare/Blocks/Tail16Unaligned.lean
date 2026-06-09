/-
B36 — 16-byte byte-by-byte unaligned tail (PCs 0x200c18..0x200c9c, 34 instr).

Copies 16 bytes from `[a4]` to `[a3]` byte-by-byte using 3 rolling
scratch registers (a1, a5, a6), then advances `a4` by 16 and stages
`a1 ← a3 + 16` for whatever follows.

The block is split into two halves of 17 instructions each so that each
unfold/extraction proof fits in the default heartbeat budget.  The full
block's facts compose from the halves' facts via `runInstrs_append`.

Triple form: strongest postcondition `s' = runInstrs s block`.  The
aliasing-sensitive memory facts are deferred to the CFG/correctness layer.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Half 1 (17 instr, PCs 0x200c18..0x200c58). -/

def block_16byte_unaligned_h1 : List Instr :=
  [ Instr.lb 11 14 0
  , Instr.lb 15 14 1
  , Instr.lb 16 14 2
  , Instr.sb 13 11 0
  , Instr.sb 13 15 1
  , Instr.lb 11 14 3
  , Instr.sb 13 16 2
  , Instr.lb 15 14 4
  , Instr.lb 16 14 5
  , Instr.sb 13 11 3
  , Instr.lb 11 14 6
  , Instr.sb 13 15 4
  , Instr.sb 13 16 5
  , Instr.lb 15 14 7
  , Instr.sb 13 11 6
  , Instr.lb 11 14 8
  , Instr.lb 16 14 9
  ]

theorem block_16byte_unaligned_h1_triple :
    Triple block_16byte_unaligned_h1
      (fun s s' => s' = runInstrs s block_16byte_unaligned_h1) :=
  Triple_sp _

private theorem unfold_post_h1 (s : State) :
    runInstrs s block_16byte_unaligned_h1
      = exec (exec (exec (exec (exec (exec (exec (exec (exec (exec (exec
          (exec (exec (exec (exec (exec (exec s
            (Instr.lb 11 14 0)) (Instr.lb 15 14 1)) (Instr.lb 16 14 2))
            (Instr.sb 13 11 0)) (Instr.sb 13 15 1)) (Instr.lb 11 14 3))
            (Instr.sb 13 16 2)) (Instr.lb 15 14 4)) (Instr.lb 16 14 5))
            (Instr.sb 13 11 3)) (Instr.lb 11 14 6)) (Instr.sb 13 15 4))
            (Instr.sb 13 16 5)) (Instr.lb 15 14 7)) (Instr.sb 13 11 6))
            (Instr.lb 11 14 8)) (Instr.lb 16 14 9) := by
  rfl

theorem block_16byte_unaligned_h1_pc (s : State) :
    (runInstrs s block_16byte_unaligned_h1).pc = s.pc + 68 := by
  rw [unfold_post_h1]
  show s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = _
  bv_decide

theorem block_16byte_unaligned_h1_a3 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h1) 13 = getReg s 13 := by
  rw [unfold_post_h1]; simp

theorem block_16byte_unaligned_h1_a4 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h1) 14 = getReg s 14 := by
  rw [unfold_post_h1]; simp

theorem block_16byte_unaligned_h1_a2 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h1) 12 = getReg s 12 := by
  rw [unfold_post_h1]; simp

theorem block_16byte_unaligned_h1_a0 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h1) 10 = getReg s 10 := by
  rw [unfold_post_h1]; simp

/-! ## Half 2 (17 instr, PCs 0x200c5c..0x200c9c). -/

def block_16byte_unaligned_h2 : List Instr :=
  [ Instr.sb   13 15 7
  , Instr.lb   15 14 10
  , Instr.sb   13 11 8
  , Instr.sb   13 16 9
  , Instr.lb   11 14 11
  , Instr.sb   13 15 10
  , Instr.lb   15 14 12
  , Instr.lb   16 14 13
  , Instr.sb   13 11 11
  , Instr.lb   11 14 14
  , Instr.sb   13 15 12
  , Instr.sb   13 16 13
  , Instr.lb   15 14 15
  , Instr.sb   13 11 14
  , Instr.addi 14 14 16
  , Instr.addi 11 13 16
  , Instr.sb   13 15 15
  ]

theorem block_16byte_unaligned_h2_triple :
    Triple block_16byte_unaligned_h2
      (fun s s' => s' = runInstrs s block_16byte_unaligned_h2) :=
  Triple_sp _

private theorem unfold_post_h2 (s : State) :
    runInstrs s block_16byte_unaligned_h2
      = exec (exec (exec (exec (exec (exec (exec (exec (exec (exec (exec
          (exec (exec (exec (exec (exec (exec s
            (Instr.sb   13 15 7)) (Instr.lb   15 14 10)) (Instr.sb   13 11 8))
            (Instr.sb   13 16 9)) (Instr.lb   11 14 11)) (Instr.sb   13 15 10))
            (Instr.lb   15 14 12)) (Instr.lb   16 14 13)) (Instr.sb   13 11 11))
            (Instr.lb   11 14 14)) (Instr.sb   13 15 12)) (Instr.sb   13 16 13))
            (Instr.lb   15 14 15)) (Instr.sb   13 11 14)) (Instr.addi 14 14 16))
            (Instr.addi 11 13 16)) (Instr.sb   13 15 15) := by
  rfl

theorem block_16byte_unaligned_h2_pc (s : State) :
    (runInstrs s block_16byte_unaligned_h2).pc = s.pc + 68 := by
  rw [unfold_post_h2]
  show s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = _
  bv_decide

theorem block_16byte_unaligned_h2_a1 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h2) 11 = getReg s 13 + 16 := by
  rw [unfold_post_h2]; simp

theorem block_16byte_unaligned_h2_a3 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h2) 13 = getReg s 13 := by
  rw [unfold_post_h2]; simp

theorem block_16byte_unaligned_h2_a4 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h2) 14 = getReg s 14 + 16 := by
  rw [unfold_post_h2]; simp

theorem block_16byte_unaligned_h2_a2 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h2) 12 = getReg s 12 := by
  rw [unfold_post_h2]; simp

theorem block_16byte_unaligned_h2_a0 (s : State) :
    getReg (runInstrs s block_16byte_unaligned_h2) 10 = getReg s 10 := by
  rw [unfold_post_h2]; simp

/-! ## The full block — concatenation of the two halves. -/

def block_16byte_unaligned : List Instr :=
  block_16byte_unaligned_h1 ++ block_16byte_unaligned_h2

/-- Structured post-condition for B36: pc and register effects.
    PC bumps by 136; `a1 ← a3 + 16`; `a4 ← a4 + 16`; `a0`, `a2`, `a3`
    preserved.

    The byte-level memory effects are captured in *separate* theorems
    (see `block_16byte_unaligned_mem_bytes` and `_mem_untouched` below)
    to avoid encumbering this R with aliasing-sensitive conjuncts. -/
def R_block_16byte_unaligned : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 136 ∧
    getReg s' 10 = getReg s 10 ∧
    getReg s' 11 = getReg s 13 + 16 ∧
    getReg s' 12 = getReg s 12 ∧
    getReg s' 13 = getReg s 13 ∧
    getReg s' 14 = getReg s 14 + 16

theorem block_16byte_unaligned_triple :
    Triple block_16byte_unaligned R_block_16byte_unaligned := by
  intro s
  unfold block_16byte_unaligned
  rw [runInstrs_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block_16byte_unaligned_h2_pc, block_16byte_unaligned_h1_pc]; bv_decide
  · rw [block_16byte_unaligned_h2_a0, block_16byte_unaligned_h1_a0]
  · rw [block_16byte_unaligned_h2_a1, block_16byte_unaligned_h1_a3]
  · rw [block_16byte_unaligned_h2_a2, block_16byte_unaligned_h1_a2]
  · rw [block_16byte_unaligned_h2_a3, block_16byte_unaligned_h1_a3]
  · rw [block_16byte_unaligned_h2_a4, block_16byte_unaligned_h1_a4]

/-! ## Byte-level memory views (separate theorems).

  The block copies 16 bytes from `[a4, a4+16)` to `[a3, a3+16)` byte by
  byte.  Loads and stores are interleaved, so the byte-copy claim
  requires the non-aliasing precondition `Pre_16byte_no_alias`. -/

/-- Non-aliasing precondition: dst window `[a3, a3+16)` disjoint from
    src window `[a4, a4+16)`. -/
def Pre_16byte_no_alias (s : State) : Prop :=
  ∀ i j : UInt32, i < 16 → j < 16 → getReg s 13 + i ≠ getReg s 14 + j

/-- Byte-copy claim: under non-aliasing, the 16 dst bytes equal the
    16 src bytes.  (Proof: chase `.mem (a3+i)` through the 34-instr
    chain, using non-aliasing to show each load reads the original
    byte; see proof sketch in `block_16byte_unaligned_h1_mem` notes.) -/
theorem block_16byte_unaligned_mem_bytes (s : State) (h : Pre_16byte_no_alias s)
    (i : UInt32) (hi : i < 16) :
    (runInstrs s block_16byte_unaligned).mem (getReg s 13 + i)
      = s.mem (getReg s 14 + i) := by
  sorry

/-- Untouched-bytes claim: any address outside `[a3, a3+16)` is preserved. -/
theorem block_16byte_unaligned_mem_untouched (s : State) (a : UInt32)
    (h : ∀ i : UInt32, i < 16 → a ≠ getReg s 13 + i) :
    (runInstrs s block_16byte_unaligned).mem a = s.mem a := by
  sorry

end MemcpyProof.Hoare
