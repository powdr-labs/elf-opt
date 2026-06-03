/-
The 8-byte tail-copy basic block from memcpy (PCs 0x200a54..0x200a68).

Six instructions copying 8 bytes from `regs 14` to `regs 13` and
advancing both pointers by 8.  Stated as a `List Instr` constant
with full Triple semantics derived compositionally — no PC, no
`code`, no memory layout.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

def block_8byte : List Instr :=
  [ Instr.lw   11 14 0
  , Instr.lw   15 14 4
  , Instr.sw   13 11 0
  , Instr.sw   13 15 4
  , Instr.addi 13 13 8
  , Instr.addi 14 14 8
  ]

theorem block_8byte_triple_composed :
    Triple block_8byte
      (RComp (fun s s' => s' = advance (setReg s 11 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s' = advance (setReg s 15 (loadWord s (getReg s 14 + 4))))
          (RComp (fun s s' => s' = advance (storeWord s (getReg s 13 + 0) (getReg s 11)))
            (RComp (fun s s' => s' = advance (storeWord s (getReg s 13 + 4) (getReg s 15)))
              (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 13 + 8)))
                    (fun s s' => s' = advance (setReg s 14 (getReg s 14 + 8))))))))  :=
  (Triple_lw   11 14 0).append <|
  (Triple_lw   15 14 4).append <|
  (Triple_sw   13 11 0).append <|
  (Triple_sw   13 15 4).append <|
  (Triple_addi 13 13 8).append <|
  (Triple_addi 14 14 8)

/-- Clean relational post-condition for `block_8byte`. -/
def R_block_8byte : State → State → Prop :=
  fun s s' =>
    let v0 : UInt32 := loadWord s (getReg s 14)
    let v4 : UInt32 := loadWord s (getReg s 14 + 4)
    s'.pc = s.pc + 24 ∧
    getReg s' 11 = v0 ∧
    getReg s' 15 = v4 ∧
    getReg s' 13 = getReg s 13 + 8 ∧
    getReg s' 14 = getReg s 14 + 8 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 15 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord (storeWord s (getReg s 13) v0) (getReg s 13 + 4) v4).mem

theorem block_8byte_triple : Triple block_8byte R_block_8byte := by
  refine Triple.weaken block_8byte_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24 := by bv_decide
  simp [R_block_8byte, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11 hr13 hr14 hr15
    simp [setReg, Ne.symm hr11, Ne.symm hr13, Ne.symm hr14, Ne.symm hr15]
  · unfold storeWord; simp [storeByte]

end MemcpyProof.Hoare
