/-
Field-projection simp lemmas for `setReg`, `advance`, `storeByte`,
`storeWord`, `loadWord`, etc.  These are the workhorses for reducing
the post-state of a chain of `exec` applications to explicit values.
-/

import MemcpyProof.Sem

namespace MemcpyProof.Hoare

open MemcpyProof.Sem

/-! ## `advance` — preserves all fields except `pc`. -/

@[simp] theorem advance_pc (s : State) : (advance s).pc = s.pc + 4 := rfl
@[simp] theorem advance_regs (s : State) : (advance s).regs = s.regs := rfl
@[simp] theorem advance_mem (s : State) : (advance s).mem = s.mem := rfl
@[simp] theorem advance_halted (s : State) : (advance s).halted = s.halted := rfl
@[simp] theorem advance_haltAt (s : State) : (advance s).haltAt = s.haltAt := rfl

/-! ## `setReg` — preserves all fields except `regs`. -/

@[simp] theorem setReg_pc (s : State) (r v : UInt32) : (setReg s r v).pc = s.pc := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_mem (s : State) (r v : UInt32) : (setReg s r v).mem = s.mem := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_halted (s : State) (r v : UInt32) : (setReg s r v).halted = s.halted := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_haltAt (s : State) (r v : UInt32) : (setReg s r v).haltAt = s.haltAt := by
  unfold setReg; split <;> rfl

/-- Reading the just-written register (for r ≠ 0).  Marked `@[simp]` so
    simp auto-discharges the `r ≠ 0` side condition by `decide` when r
    is a concrete numeric literal. -/
@[simp] theorem setReg_regs_same (s : State) (r v : UInt32) (h : r ≠ 0) :
    (setReg s r v).regs r = v := by
  unfold setReg
  rw [if_neg]
  · show (fun i => if i == r then v else s.regs i) r = v
    simp
  · intro contra; exact h (by simpa using contra)

/-- Reading a different register (frame).  Marked `@[simp]` so simp
    auto-discharges the `r' ≠ r` side condition by `decide` for literal
    register numbers, or via the user-provided hypothesis. -/
@[simp] theorem setReg_regs_other (s : State) (r r' v : UInt32) (h : r' ≠ r) :
    (setReg s r v).regs r' = s.regs r' := by
  unfold setReg
  split
  · rfl
  · show (if r' == r then v else s.regs r') = s.regs r'
    rw [if_neg]
    intro contra; exact h (by simpa using contra)

/-- `setReg` to register 0 is a no-op (x0 is hardwired to 0). -/
@[simp] theorem setReg_zero (s : State) (v : UInt32) : setReg s 0 v = s := by
  unfold setReg; simp

/-! ## `getReg` reduces predictably. -/

theorem getReg_zero (s : State) : getReg s 0 = 0 := by unfold getReg; rfl

theorem getReg_nonzero (s : State) (r : UInt32) (h : r ≠ 0) :
    getReg s r = s.regs r := by
  unfold getReg
  rw [if_neg]
  intro contra; exact h (by simpa using contra)

/-! ## `loadWord`/`loadByte` only depend on `.mem`, which `advance`/`setReg`
preserve. -/

@[simp] theorem loadByte_advance (s : State) (a : UInt32) :
    loadByte (advance s) a = loadByte s a := rfl

@[simp] theorem loadByte_setReg (s : State) (r v a : UInt32) :
    loadByte (setReg s r v) a = loadByte s a := by unfold loadByte setReg; split <;> rfl

@[simp] theorem loadWord_advance (s : State) (a : UInt32) :
    loadWord (advance s) a = loadWord s a := by unfold loadWord; simp

@[simp] theorem loadWord_setReg (s : State) (r v a : UInt32) :
    loadWord (setReg s r v) a = loadWord s a := by unfold loadWord; simp

/-! ## `getReg` propagates through state updates. -/

@[simp] theorem getReg_advance (s : State) (r : UInt32) :
    getReg (advance s) r = getReg s r := by unfold getReg; rfl

@[simp] theorem getReg_storeByte (s : State) (a : UInt32) (b : UInt8) (r : UInt32) :
    getReg (storeByte s a b) r = getReg s r := by unfold getReg; rfl

@[simp] theorem getReg_storeWord (s : State) (a v r : UInt32) :
    getReg (storeWord s a v) r = getReg s r := by
  unfold storeWord; simp

@[simp] theorem getReg_setReg_same (s : State) (r v : UInt32) (h : r ≠ 0) :
    getReg (setReg s r v) r = v := by
  rw [getReg_nonzero _ _ h]
  exact setReg_regs_same s r v h

@[simp] theorem getReg_setReg_other (s : State) (r r' v : UInt32) (h : r' ≠ r) (h0 : r' ≠ 0) :
    getReg (setReg s r v) r' = getReg s r' := by
  rw [getReg_nonzero _ _ h0, getReg_nonzero _ _ h0]
  exact setReg_regs_other s r r' v h

/-! ## `storeByte` — preserves all fields except `mem`. -/

@[simp] theorem storeByte_pc (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).pc = s.pc := rfl
@[simp] theorem storeByte_regs (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).regs = s.regs := rfl
@[simp] theorem storeByte_halted (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).halted = s.halted := rfl
@[simp] theorem storeByte_haltAt (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).haltAt = s.haltAt := rfl

/-! ## `storeWord` — preserves all fields except `mem`. -/

@[simp] theorem storeWord_pc (s : State) (a v : UInt32) :
    (storeWord s a v).pc = s.pc := by unfold storeWord; simp
@[simp] theorem storeWord_regs (s : State) (a v : UInt32) :
    (storeWord s a v).regs = s.regs := by unfold storeWord; simp
@[simp] theorem storeWord_halted (s : State) (a v : UInt32) :
    (storeWord s a v).halted = s.halted := by unfold storeWord; simp
@[simp] theorem storeWord_haltAt (s : State) (a v : UInt32) :
    (storeWord s a v).haltAt = s.haltAt := by unfold storeWord; simp

/-! ## `exec` preserves `halted` for non-branch, non-jump instruction
classes — `simp` lemmas that let `runInstrs_cons_not_halted` chain
through a basic block. -/

open MemcpyProof.RV32I in
@[simp] theorem exec_addi_halted (s : State) (rd rs1 imm : UInt32) :
    (exec s (Instr.addi rd rs1 imm)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 + imm))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_andi_halted (s : State) (rd rs1 imm : UInt32) :
    (exec s (Instr.andi rd rs1 imm)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 &&& imm))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_ori_halted (s : State) (rd rs1 imm : UInt32) :
    (exec s (Instr.ori rd rs1 imm)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 ||| imm))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_slli_halted (s : State) (rd rs1 sh : UInt32) :
    (exec s (Instr.slli rd rs1 sh)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 <<< sh))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_srli_halted (s : State) (rd rs1 sh : UInt32) :
    (exec s (Instr.srli rd rs1 sh)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 >>> sh))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_sltiu_halted (s : State) (rd rs1 imm : UInt32) :
    (exec s (Instr.sltiu rd rs1 imm)).halted = s.halted := by
  show (advance (setReg s rd _)).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_and_halted (s : State) (rd rs1 rs2 : UInt32) :
    (exec s (Instr.and_ rd rs1 rs2)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 &&& getReg s rs2))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_or_halted (s : State) (rd rs1 rs2 : UInt32) :
    (exec s (Instr.or_ rd rs1 rs2)).halted = s.halted := by
  show (advance (setReg s rd (getReg s rs1 ||| getReg s rs2))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_sltu_halted (s : State) (rd rs1 rs2 : UInt32) :
    (exec s (Instr.sltu rd rs1 rs2)).halted = s.halted := by
  show (advance (setReg s rd _)).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_lb_halted (s : State) (rd rs1 imm : UInt32) :
    (exec s (Instr.lb rd rs1 imm)).halted = s.halted := by
  show (advance (setReg s rd _)).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_lw_halted (s : State) (rd rs1 imm : UInt32) :
    (exec s (Instr.lw rd rs1 imm)).halted = s.halted := by
  show (advance (setReg s rd (loadWord s (getReg s rs1 + imm)))).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_sw_halted (s : State) (rs1 rs2 imm : UInt32) :
    (exec s (Instr.sw rs1 rs2 imm)).halted = s.halted := by
  show (advance (storeWord s _ _)).halted = s.halted
  simp

open MemcpyProof.RV32I in
@[simp] theorem exec_sb_halted (s : State) (rs1 rs2 imm : UInt32) :
    (exec s (Instr.sb rs1 rs2 imm)).halted = s.halted := by
  show (advance (storeByte s _ _)).halted = s.halted
  simp

end MemcpyProof.Hoare
