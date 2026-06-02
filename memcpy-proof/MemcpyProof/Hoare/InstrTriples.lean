/-
Per-instruction Hoare triples — the atomic building blocks.

For each `Instr` constructor used by memcpy, a `Triple [Instr.<class> args] R`
where `R` is the strongest postcondition: `s' = exec s (Instr.<class> args)`
under the non-halted precondition.

These are *parametric in instruction arguments*, not per-PC.  One lemma
per instruction class — covers every PC where that class is used.
-/

import MemcpyProof.Hoare.Triple
import MemcpyProof.Hoare.InstrEqns

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-- The generic per-instruction Triple template: the post-state is
    `exec s i` when not halted. -/
theorem Triple_instr (i : Instr) :
    Triple [i] (fun s s' => s.halted = false → s' = exec s i) := by
  intro s h
  show (if s.halted then s else runInstrs (exec s i) []) = exec s i
  rw [h]; rfl

/-! ## Instruction-class triples, with the post-state spelled out. -/

theorem Triple_addi (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.addi rd rs1 imm]
      (fun s s' => s.halted = false →
        s' = advance (setReg s rd (getReg s rs1 + imm))) := by
  intro s h
  rw [show (advance (setReg s rd (getReg s rs1 + imm))) = exec s (Instr.addi rd rs1 imm) from
        (exec_addi s rd rs1 imm).symm]
  exact Triple_instr _ s h

theorem Triple_andi (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.andi rd rs1 imm]
      (fun s s' => s.halted = false →
        s' = advance (setReg s rd (getReg s rs1 &&& imm))) := by
  intro s h
  rw [show (advance (setReg s rd (getReg s rs1 &&& imm))) = exec s (Instr.andi rd rs1 imm) from
        (exec_andi s rd rs1 imm).symm]
  exact Triple_instr _ s h

theorem Triple_ori (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.ori rd rs1 imm]
      (fun s s' => s.halted = false →
        s' = advance (setReg s rd (getReg s rs1 ||| imm))) := by
  intro s h
  rw [show (advance (setReg s rd (getReg s rs1 ||| imm))) = exec s (Instr.ori rd rs1 imm) from
        (exec_ori s rd rs1 imm).symm]
  exact Triple_instr _ s h

theorem Triple_slli (rd rs1 : Reg) (sh : UInt32) :
    Triple [Instr.slli rd rs1 sh]
      (fun s s' => s.halted = false →
        s' = advance (setReg s rd (getReg s rs1 <<< sh))) := by
  intro s h
  rw [show (advance (setReg s rd (getReg s rs1 <<< sh))) = exec s (Instr.slli rd rs1 sh) from
        (exec_slli s rd rs1 sh).symm]
  exact Triple_instr _ s h

theorem Triple_srli (rd rs1 : Reg) (sh : UInt32) :
    Triple [Instr.srli rd rs1 sh]
      (fun s s' => s.halted = false →
        s' = advance (setReg s rd (getReg s rs1 >>> sh))) := by
  intro s h
  rw [show (advance (setReg s rd (getReg s rs1 >>> sh))) = exec s (Instr.srli rd rs1 sh) from
        (exec_srli s rd rs1 sh).symm]
  exact Triple_instr _ s h

theorem Triple_lw (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.lw rd rs1 imm]
      (fun s s' => s.halted = false →
        s' = advance (setReg s rd (loadWord s (getReg s rs1 + imm)))) := by
  intro s h
  rw [show (advance (setReg s rd (loadWord s (getReg s rs1 + imm))))
          = exec s (Instr.lw rd rs1 imm) from
        (exec_lw s rd rs1 imm).symm]
  exact Triple_instr _ s h

theorem Triple_sw (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.sw rs1 rs2 imm]
      (fun s s' => s.halted = false →
        s' = advance (storeWord s (getReg s rs1 + imm) (getReg s rs2))) := by
  intro s h
  rw [show (advance (storeWord s (getReg s rs1 + imm) (getReg s rs2)))
          = exec s (Instr.sw rs1 rs2 imm) from
        (exec_sw s rs1 rs2 imm).symm]
  exact Triple_instr _ s h

theorem Triple_sb (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.sb rs1 rs2 imm]
      (fun s s' => s.halted = false →
        s' = advance (storeByte s (getReg s rs1 + imm) (getReg s rs2).toUInt8)) := by
  intro s h
  rw [show (advance (storeByte s (getReg s rs1 + imm) (getReg s rs2).toUInt8))
          = exec s (Instr.sb rs1 rs2 imm) from
        (exec_sb s rs1 rs2 imm).symm]
  exact Triple_instr _ s h

end MemcpyProof.Hoare
