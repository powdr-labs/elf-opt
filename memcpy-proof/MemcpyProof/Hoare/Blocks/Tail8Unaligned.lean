/-
B38 — 8-byte byte-by-byte unaligned tail (PCs 0x200cac..0x200cf0, 18 instr).

Copies 8 bytes from `[a4]` to `[a3]` one byte at a time using 3 rolling
scratch registers (a1, a5, a6), then advances `a4` by 8 and stages
`a1 ← a3 + 8` for whatever follows.

Because lb's appear *after* sb's within the block, an unconditional clean
post-condition would need to track aliasing.  We sidestep that by giving
the **strongest postcondition** form `s' = runInstrs s block`, and then
proving a few high-level extraction lemmas (pc bump, key register values,
frame) by direct simp on the explicit exec-chain.
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

/-- The semantics of B38 in strongest-postcondition form. -/
theorem block_8byte_unaligned_triple :
    Triple block_8byte_unaligned
      (fun s s' => s' = runInstrs s block_8byte_unaligned) :=
  Triple_sp _

/-! ## Extraction lemmas — useful facts about the post-state. -/

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

theorem block_8byte_unaligned_pc (s : State) :
    (runInstrs s block_8byte_unaligned).pc = s.pc + 72 := by
  rw [unfold_post]
  show s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 = _
  bv_decide

theorem block_8byte_unaligned_a1 (s : State) :
    getReg (runInstrs s block_8byte_unaligned) 11 = getReg s 13 + 8 := by
  rw [unfold_post]; simp

theorem block_8byte_unaligned_a3 (s : State) :
    getReg (runInstrs s block_8byte_unaligned) 13 = getReg s 13 := by
  rw [unfold_post]; simp

theorem block_8byte_unaligned_a4 (s : State) :
    getReg (runInstrs s block_8byte_unaligned) 14 = getReg s 14 + 8 := by
  rw [unfold_post]; simp

theorem block_8byte_unaligned_a2 (s : State) :
    getReg (runInstrs s block_8byte_unaligned) 12 = getReg s 12 := by
  rw [unfold_post]; simp

theorem block_8byte_unaligned_a0 (s : State) :
    getReg (runInstrs s block_8byte_unaligned) 10 = getReg s 10 := by
  rw [unfold_post]; simp

end MemcpyProof.Hoare
