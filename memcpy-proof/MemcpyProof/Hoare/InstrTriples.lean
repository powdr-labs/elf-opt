/-
Per-instruction Hoare triples — the atomic building blocks.

For each `Instr` constructor used by memcpy, a `Triple [Instr.<class> args] R`
where `R` is the strongest postcondition: `s' = exec s (Instr.<class> args)`.

These are *parametric in instruction arguments*, not per-PC.  One lemma
per instruction class — covers every PC where that class is used.
-/

import MemcpyProof.Hoare.Triple
import MemcpyProof.Hoare.InstrEqns

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Instruction-class triples, with the post-state spelled out. -/

theorem Triple_addi (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.addi rd rs1 imm]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 + imm))) := by
  intro s; exact (exec_addi s rd rs1 imm).symm

theorem Triple_andi (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.andi rd rs1 imm]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 &&& imm))) := by
  intro s; exact (exec_andi s rd rs1 imm).symm

theorem Triple_ori (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.ori rd rs1 imm]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 ||| imm))) := by
  intro s; exact (exec_ori s rd rs1 imm).symm

theorem Triple_slli (rd rs1 : Reg) (sh : UInt32) :
    Triple [Instr.slli rd rs1 sh]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 <<< sh))) := by
  intro s; exact (exec_slli s rd rs1 sh).symm

theorem Triple_srli (rd rs1 : Reg) (sh : UInt32) :
    Triple [Instr.srli rd rs1 sh]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 >>> sh))) := by
  intro s; exact (exec_srli s rd rs1 sh).symm

theorem Triple_sltiu (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.sltiu rd rs1 imm]
      (fun s s' => s' = advance (setReg s rd (if getReg s rs1 < imm then 1 else 0))) := by
  intro s; exact (exec_sltiu s rd rs1 imm).symm

theorem Triple_or (rd rs1 rs2 : Reg) :
    Triple [Instr.or_ rd rs1 rs2]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 ||| getReg s rs2))) := by
  intro s; exact (exec_or s rd rs1 rs2).symm

theorem Triple_and (rd rs1 rs2 : Reg) :
    Triple [Instr.and_ rd rs1 rs2]
      (fun s s' => s' = advance (setReg s rd (getReg s rs1 &&& getReg s rs2))) := by
  intro s; exact (exec_and s rd rs1 rs2).symm

theorem Triple_sltu (rd rs1 rs2 : Reg) :
    Triple [Instr.sltu rd rs1 rs2]
      (fun s s' => s' = advance (setReg s rd (if getReg s rs1 < getReg s rs2 then 1 else 0))) := by
  intro s; exact (exec_sltu s rd rs1 rs2).symm

theorem Triple_lw (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.lw rd rs1 imm]
      (fun s s' => s' = advance (setReg s rd (loadWord s (getReg s rs1 + imm)))) := by
  intro s; exact (exec_lw s rd rs1 imm).symm

theorem Triple_lb (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.lb rd rs1 imm]
      (fun s s' => s' = advance (setReg s rd
                          (signExt (loadByte s (getReg s rs1 + imm)).toUInt32 7))) := by
  intro s; exact (exec_lb s rd rs1 imm).symm

theorem Triple_sw (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.sw rs1 rs2 imm]
      (fun s s' => s' = advance (storeWord s (getReg s rs1 + imm) (getReg s rs2))) := by
  intro s; exact (exec_sw s rs1 rs2 imm).symm

theorem Triple_sb (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.sb rs1 rs2 imm]
      (fun s s' => s' = advance (storeByte s (getReg s rs1 + imm) (getReg s rs2).toUInt8)) := by
  intro s; exact (exec_sb s rs1 rs2 imm).symm

theorem Triple_bne (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.bne rs1 rs2 imm]
      (fun s s' => s' =
        if getReg s rs1 != getReg s rs2 then jumpTo s (s.pc + imm) else advance s) := by
  intro s; exact (exec_bne s rs1 rs2 imm).symm

theorem Triple_beq (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.beq rs1 rs2 imm]
      (fun s s' => s' =
        if getReg s rs1 == getReg s rs2 then jumpTo s (s.pc + imm) else advance s) := by
  intro s; exact (exec_beq s rs1 rs2 imm).symm

theorem Triple_bltu (rs1 rs2 : Reg) (imm : UInt32) :
    Triple [Instr.bltu rs1 rs2 imm]
      (fun s s' => s' =
        if getReg s rs1 < getReg s rs2 then jumpTo s (s.pc + imm) else advance s) := by
  intro s; exact (exec_bltu s rs1 rs2 imm).symm

theorem Triple_jal (rd : Reg) (imm : UInt32) :
    Triple [Instr.jal rd imm]
      (fun s s' => s' = jumpTo (setReg s rd (s.pc + 4)) (s.pc + imm)) := by
  intro s; exact (exec_jal s rd imm).symm

theorem Triple_jalr (rd rs1 : Reg) (imm : UInt32) :
    Triple [Instr.jalr rd rs1 imm]
      (fun s s' => s' = jumpTo (setReg s rd (s.pc + 4))
                          ((getReg s rs1 + imm) &&& (~~~ 1))) := by
  intro s; exact (exec_jalr s rd rs1 imm).symm

end MemcpyProof.Hoare
