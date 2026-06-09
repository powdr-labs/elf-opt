/-
B38 — 8-byte byte-by-byte unaligned tail (PCs 0x200cac..0x200cf0, 18 instr).

Copies 8 bytes from `[a4]` to `[a3]` one byte at a time, advances `a4`
by 8, and stages `a1 ← a3 + 8`.

Triple's structured `R` captures the unconditional register/pc facts.
The byte-copy memory effect is aliasing-sensitive (the loop reads from
addresses some of which were just stored to) and is deferred to the
correctness layer where a non-overlap assumption is in scope.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

def block_8byte_unaligned : List Instr :=
  [ Instr.lb   11 14 0
  , Instr.lb   15 14 1
  , Instr.lb   16 14 2
  , Instr.sb   13 11 0
  , Instr.sb   13 15 1
  , Instr.lb   11 14 3
  , Instr.sb   13 16 2
  , Instr.lb   15 14 4
  , Instr.lb   16 14 5
  , Instr.sb   13 11 3
  , Instr.lb   11 14 6
  , Instr.sb   13 15 4
  , Instr.sb   13 16 5
  , Instr.lb   15 14 7
  , Instr.sb   13 11 6
  , Instr.addi 14 14 8
  , Instr.addi 11 13 8
  , Instr.sb   13 15 7
  ]

private theorem unfold_post (s : State) :
    runInstrs s block_8byte_unaligned
      = exec (exec (exec (exec (exec (exec (exec (exec (exec
          (exec (exec (exec (exec (exec (exec (exec (exec (exec s
            (Instr.lb 11 14 0)) (Instr.lb 15 14 1)) (Instr.lb 16 14 2))
            (Instr.sb 13 11 0)) (Instr.sb 13 15 1)) (Instr.lb 11 14 3))
            (Instr.sb 13 16 2)) (Instr.lb 15 14 4)) (Instr.lb 16 14 5))
            (Instr.sb 13 11 3)) (Instr.lb 11 14 6)) (Instr.sb 13 15 4))
            (Instr.sb 13 16 5)) (Instr.lb 15 14 7)) (Instr.sb 13 11 6))
            (Instr.addi 14 14 8)) (Instr.addi 11 13 8)) (Instr.sb 13 15 7) := by
  rfl

/-- Structured post-condition: pc bumps by 72; `a1 ← a3 + 8`; `a4 ← a4 + 8`;
    `a0`, `a2`, `a3` preserved.  Byte-level memory views are in separate
    theorems below (see `block_8byte_unaligned_mem_bytes`). -/
def R_block_8byte_unaligned : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 72 ∧
    getReg s' 10 = getReg s 10 ∧
    getReg s' 11 = getReg s 13 + 8 ∧
    getReg s' 12 = getReg s 12 ∧
    getReg s' 13 = getReg s 13 ∧
    getReg s' 14 = getReg s 14 + 8

theorem block_8byte_unaligned_triple :
    Triple block_8byte_unaligned R_block_8byte_unaligned := by
  intro s
  rw [show runInstrs s block_8byte_unaligned = _ from unfold_post s]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = _
    bv_decide
  · simp
  · simp
  · simp
  · simp
  · simp

/-! ## Byte-level memory views (separate theorems). -/

/-- Non-aliasing precondition: dst window `[a3, a3+8)` disjoint from
    src window `[a4, a4+8)`. -/
def Pre_8byte_no_alias (s : State) : Prop :=
  ∀ i j : UInt32, i < 8 → j < 8 → getReg s 13 + i ≠ getReg s 14 + j

/-- Byte-copy claim: under non-aliasing, the 8 dst bytes equal the
    8 src bytes. -/
theorem block_8byte_unaligned_mem_bytes (s : State) (h : Pre_8byte_no_alias s)
    (i : UInt32) (hi : i < 8) :
    (runInstrs s block_8byte_unaligned).mem (getReg s 13 + i)
      = s.mem (getReg s 14 + i) := by
  sorry

/-- Untouched-bytes claim: any address outside `[a3, a3+8)` is preserved. -/
theorem block_8byte_unaligned_mem_untouched (s : State) (a : UInt32)
    (h : ∀ i : UInt32, i < 8 → a ≠ getReg s 13 + i) :
    (runInstrs s block_8byte_unaligned).mem a = s.mem a := by
  sorry

end MemcpyProof.Hoare
