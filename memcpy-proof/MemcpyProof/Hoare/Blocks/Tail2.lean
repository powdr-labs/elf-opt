/-
The 2-byte tail block (memcpy PCs 0x200be8..0x200bfc) — B32.

  lb   a1, 0(a4)    -- a1 ← signExt(Mem[a4])
  lb   a5, 1(a4)    -- a5 ← signExt(Mem[a4+1])
  sb   a1, 0(a3)    -- Mem[a3]   ← (a1 as UInt8)
  addi a4, a4, 2    -- a4 ← a4 + 2
  addi a1, a3, 2    -- a1 ← a3 + 2  (overwrites the just-loaded value)
  sb   a5, 1(a3)    -- Mem[a3+1] ← (a5 as UInt8)
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

def block_2byte_tail : List Instr :=
  [ Instr.lb   11 14 0
  , Instr.lb   15 14 1
  , Instr.sb   13 11 0
  , Instr.addi 14 14 2
  , Instr.addi 11 13 2
  , Instr.sb   13 15 1
  ]

theorem block_2byte_tail_triple_composed :
    Triple block_2byte_tail
      (RComp (fun s s' => s' = advance (setReg s 11
                        (signExt (loadByte s (getReg s 14 + 0)).toUInt32 7)))
        (RComp (fun s s' => s' = advance (setReg s 15
                          (signExt (loadByte s (getReg s 14 + 1)).toUInt32 7)))
          (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 0) (getReg s 11).toUInt8))
            (RComp (fun s s' => s' = advance (setReg s 14 (getReg s 14 + 2)))
              (RComp (fun s s' => s' = advance (setReg s 11 (getReg s 13 + 2)))
                (fun s s' => s' = advance (storeByte s (getReg s 13 + 1) (getReg s 15).toUInt8)))))))  :=
  (Triple_lb   11 14 0).append <|
  (Triple_lb   15 14 1).append <|
  (Triple_sb   13 11 0).append <|
  (Triple_addi 14 14 2).append <|
  (Triple_addi 11 13 2).append <|
  (Triple_sb   13 15 1)

def R_block_2byte_tail : State → State → Prop :=
  fun s s' =>
    let b0 : UInt32 := signExt (loadByte s (getReg s 14)).toUInt32 7
    let b1 : UInt32 := signExt (loadByte s (getReg s 14 + 1)).toUInt32 7
    s'.pc = s.pc + 24 ∧
    getReg s' 11 = getReg s 13 + 2 ∧
    getReg s' 14 = getReg s 14 + 2 ∧
    getReg s' 15 = b1 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 14 → r.val ≠ 15 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte (storeByte s (getReg s 13) b0.toUInt8)
                        (getReg s 13 + 1) b1.toUInt8).mem

theorem block_2byte_tail_triple : Triple block_2byte_tail R_block_2byte_tail := by
  refine Triple.weaken block_2byte_tail_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24 := by bv_decide
  simp [R_block_2byte_tail, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11 hr14 hr15
    simp [setReg, Ne.symm hr11, Ne.symm hr14, Ne.symm hr15]
  · unfold storeByte; simp

end MemcpyProof.Hoare
