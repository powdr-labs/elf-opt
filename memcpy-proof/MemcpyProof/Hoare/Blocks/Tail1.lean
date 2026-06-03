/-
The 1-byte tail block (memcpy PCs 0x200c0c..0x200c10) — B34.

  lb a1, 0(a4)   -- a1 ← signExt(Mem[a4])     (a1 = x11, a4 = x14)
  sb a1, 0(a3)   -- Mem[a3] ← (a1 as UInt8)   (a3 = x13)
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

def block_1byte_tail : List Instr :=
  [ Instr.lb 11 14 0
  , Instr.sb 13 11 0
  ]

theorem block_1byte_tail_triple_composed :
    Triple block_1byte_tail
      (RComp (fun s s' => s' = advance (setReg s 11
                        (signExt (loadByte s (getReg s 14 + 0)).toUInt32 7)))
             (fun s s' => s' = advance (storeByte s (getReg s 13 + 0) (getReg s 11).toUInt8))) :=
  (Triple_lb 11 14 0).append (Triple_sb 13 11 0)

def R_block_1byte_tail : State → State → Prop :=
  fun s s' =>
    let extended : UInt32 := signExt (loadByte s (getReg s 14)).toUInt32 7
    s'.pc = s.pc + 8 ∧
    getReg s' 11 = extended ∧
    (∀ r : Fin 32, r.val ≠ 11 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s (getReg s 13) extended.toUInt8).mem

theorem block_1byte_tail_triple : Triple block_1byte_tail R_block_1byte_tail := by
  refine Triple.weaken block_1byte_tail_triple_composed ?_
  rintro s s' ⟨_, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 = s.pc + 8 := by bv_decide
  simp [R_block_1byte_tail, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11
    simp [setReg, Ne.symm hr11]
  · unfold storeByte; simp

end MemcpyProof.Hoare
