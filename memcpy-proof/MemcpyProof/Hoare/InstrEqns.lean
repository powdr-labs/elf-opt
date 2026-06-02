/-
Per-instruction-class semantic equations.

For each `Instr` constructor used by memcpy, an equation
`exec s (Instr.<class> args) = <body in terms of advance/setReg/etc.>`.

These are the "what each instruction does" facts.  Each is a one-line
`rfl` because we're literally restating the corresponding match arm of
`exec` from `Sem.lean`.

Coverage matches what memcpy uses: addi, andi, ori, slli, srli, sltiu,
and_, or_, sltu, lb, lw, sw, sb, beq, bne, bltu, jal, jalr.
-/

import MemcpyProof.Sem

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Reg-write ALU instructions (I-type). -/

theorem exec_addi (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.addi rd rs1 imm) = advance (setReg s rd (getReg s rs1 + imm)) := rfl

theorem exec_andi (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.andi rd rs1 imm) = advance (setReg s rd (getReg s rs1 &&& imm)) := rfl

theorem exec_ori (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.ori rd rs1 imm) = advance (setReg s rd (getReg s rs1 ||| imm)) := rfl

theorem exec_slli (s : State) (rd rs1 sh : UInt32) :
    exec s (Instr.slli rd rs1 sh) = advance (setReg s rd (getReg s rs1 <<< sh)) := rfl

theorem exec_srli (s : State) (rd rs1 sh : UInt32) :
    exec s (Instr.srli rd rs1 sh) = advance (setReg s rd (getReg s rs1 >>> sh)) := rfl

theorem exec_sltiu (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.sltiu rd rs1 imm)
    = advance (setReg s rd (if getReg s rs1 < imm then 1 else 0)) := rfl

/-! ## R-type ALU. -/

theorem exec_and (s : State) (rd rs1 rs2 : UInt32) :
    exec s (Instr.and_ rd rs1 rs2) = advance (setReg s rd (getReg s rs1 &&& getReg s rs2)) := rfl

theorem exec_or (s : State) (rd rs1 rs2 : UInt32) :
    exec s (Instr.or_ rd rs1 rs2) = advance (setReg s rd (getReg s rs1 ||| getReg s rs2)) := rfl

theorem exec_sltu (s : State) (rd rs1 rs2 : UInt32) :
    exec s (Instr.sltu rd rs1 rs2)
    = advance (setReg s rd (if getReg s rs1 < getReg s rs2 then 1 else 0)) := rfl

/-! ## Loads. -/

theorem exec_lb (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.lb rd rs1 imm)
    = advance (setReg s rd (signExt (loadByte s (getReg s rs1 + imm)).toUInt32 7)) := rfl

theorem exec_lw (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.lw rd rs1 imm) = advance (setReg s rd (loadWord s (getReg s rs1 + imm))) := rfl

/-! ## Stores. -/

theorem exec_sw (s : State) (rs1 rs2 imm : UInt32) :
    exec s (Instr.sw rs1 rs2 imm)
    = advance (storeWord s (getReg s rs1 + imm) (getReg s rs2)) := rfl

theorem exec_sb (s : State) (rs1 rs2 imm : UInt32) :
    exec s (Instr.sb rs1 rs2 imm)
    = advance (storeByte s (getReg s rs1 + imm) (getReg s rs2).toUInt8) := rfl

/-! ## Branches.

The branch instructions take a step that either jumps (to `s.pc + imm`)
or falls through (to `s.pc + 4`), depending on the condition.  Both
outcomes are guarded by a halt check against `s.haltAt`. -/

theorem exec_bne (s : State) (rs1 rs2 imm : UInt32) :
    exec s (Instr.bne rs1 rs2 imm)
    = if getReg s rs1 != getReg s rs2 then jumpTo s (s.pc + imm) else advance s := rfl

theorem exec_beq (s : State) (rs1 rs2 imm : UInt32) :
    exec s (Instr.beq rs1 rs2 imm)
    = if getReg s rs1 == getReg s rs2 then jumpTo s (s.pc + imm) else advance s := rfl

theorem exec_bltu (s : State) (rs1 rs2 imm : UInt32) :
    exec s (Instr.bltu rs1 rs2 imm)
    = if getReg s rs1 < getReg s rs2 then jumpTo s (s.pc + imm) else advance s := rfl

/-! ## Jumps. -/

theorem exec_jal (s : State) (rd imm : UInt32) :
    exec s (Instr.jal rd imm) = jumpTo (setReg s rd (s.pc + 4)) (s.pc + imm) := rfl

theorem exec_jalr (s : State) (rd rs1 imm : UInt32) :
    exec s (Instr.jalr rd rs1 imm)
    = jumpTo (setReg s rd (s.pc + 4)) ((getReg s rs1 + imm) &&& (~~~ 1)) := rfl

end MemcpyProof.Hoare
