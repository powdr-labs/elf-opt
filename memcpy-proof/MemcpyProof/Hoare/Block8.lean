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

/-! ## The 8-byte tail-copy block.

  lw   a1, 0(a4)    -- a1 ← Mem[a4]       (a1 = x11, a4 = x14)
  lw   a5, 4(a4)    -- a5 ← Mem[a4+4]     (a5 = x15)
  sw   a1, 0(a3)    -- Mem[a3]   ← a1     (a3 = x13)
  sw   a5, 4(a3)    -- Mem[a3+4] ← a5
  addi a3, a3, 8    -- a3 += 8
  addi a4, a4, 8    -- a4 += 8 -/

def block_8byte : List Instr :=
  [ Instr.lw   11 14 0
  , Instr.lw   15 14 4
  , Instr.sw   13 11 0
  , Instr.sw   13 15 4
  , Instr.addi 13 13 8
  , Instr.addi 14 14 8
  ]

/-! ## The composed Triple. -/

theorem block_8byte_triple_composed :
    Triple block_8byte
      (RComp (fun s s' => s.halted = false →
                s' = advance (setReg s 11 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s.halted = false →
                  s' = advance (setReg s 15 (loadWord s (getReg s 14 + 4))))
          (RComp (fun s s' => s.halted = false →
                    s' = advance (storeWord s (getReg s 13 + 0) (getReg s 11)))
            (RComp (fun s s' => s.halted = false →
                      s' = advance (storeWord s (getReg s 13 + 4) (getReg s 15)))
              (RComp (fun s s' => s.halted = false →
                        s' = advance (setReg s 13 (getReg s 13 + 8)))
                    (fun s s' => s.halted = false →
                        s' = advance (setReg s 14 (getReg s 14 + 8)))))))) :=
  (Triple_lw   11 14 0).append <|
  (Triple_lw   15 14 4).append <|
  (Triple_sw   13 11 0).append <|
  (Triple_sw   13 15 4).append <|
  (Triple_addi 13 13 8).append <|
  (Triple_addi 14 14 8)

/-! ## The clean Triple. -/

/-- Clean relational post-condition for `block_8byte`. -/
def R_block_8byte : State → State → Prop :=
  fun s s' =>
    s.halted = false →
    let v0 : UInt32 := loadWord s (getReg s 14)
    let v4 : UInt32 := loadWord s (getReg s 14 + 4)
    s'.pc = s.pc + 24 ∧
    s'.halted = false ∧
    s'.haltAt = s.haltAt ∧
    getReg s' 11 = v0 ∧
    getReg s' 15 = v4 ∧
    getReg s' 13 = getReg s 13 + 8 ∧
    getReg s' 14 = getReg s 14 + 8 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 15 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord (storeWord s (getReg s 13) v0) (getReg s 13 + 4) v4).mem

theorem block_8byte_triple : Triple block_8byte R_block_8byte := by
  refine Triple.weaken block_8byte_triple_composed ?_
  rintro s s' ⟨s1, h_s1, s2, h_s2, s3, h_s3, s4, h_s4, s5, h_s5, h_s'⟩ h_halted
  have e1 := h_s1 h_halted;             subst e1
  have e2 := h_s2 (by simp [h_halted]); subst e2
  have e3 := h_s3 (by simp [h_halted]); subst e3
  have e4 := h_s4 (by simp [h_halted]); subst e4
  have e5 := h_s5 (by simp [h_halted]); subst e5
  have e' := h_s' (by simp [h_halted]); subst e'
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24; bv_decide
  · simp [h_halted]
  · simp (config := { decide := true })
  · simp (config := { decide := true })
  · simp (config := { decide := true })
  · simp (config := { decide := true })
  · intro r hr11 hr13 hr14 hr15
    simp (config := { decide := true })
      [setReg, Vector.getElem_set_ne,
       Ne.symm hr11, Ne.symm hr13, Ne.symm hr14, Ne.symm hr15]
  · simp (config := { decide := true })
    unfold storeWord
    simp [storeByte]

end MemcpyProof.Hoare
