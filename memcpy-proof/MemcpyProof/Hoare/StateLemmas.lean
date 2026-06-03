/-
Field-projection simp lemmas for `setReg`, `advance`, `storeByte`,
`storeWord`, `loadWord`, etc.  These are the workhorses for reducing
the post-state of a chain of `exec` applications to explicit values.

`Regs` is `Vector UInt32 32`, register operands are `Reg := Fin 32`,
register lookups go via `s.regs[r.val]`.
-/

import MemcpyProof.Sem

namespace MemcpyProof.Hoare

open MemcpyProof.Sem

/-! ## Coercion `(n : Reg) → Nat` evaluates for literals.

Each of the 32 register indices has its own `@[simp]` lemma saying
`((n : Reg) : Nat) = n`.  This lets simp peel `Vector.set/getElem`
side conditions like `(↑(11 : Reg) : Nat) ≠ r.val` down to
`(11 : Nat) ≠ r.val`, which matches `Fin 32`-quantified frame
hypotheses directly. -/

@[simp] theorem Reg.val_0 : ((0 : Reg) : Nat) = 0 := rfl
@[simp] theorem Reg.val_1 : ((1 : Reg) : Nat) = 1 := rfl
@[simp] theorem Reg.val_2 : ((2 : Reg) : Nat) = 2 := rfl
@[simp] theorem Reg.val_3 : ((3 : Reg) : Nat) = 3 := rfl
@[simp] theorem Reg.val_4 : ((4 : Reg) : Nat) = 4 := rfl
@[simp] theorem Reg.val_5 : ((5 : Reg) : Nat) = 5 := rfl
@[simp] theorem Reg.val_6 : ((6 : Reg) : Nat) = 6 := rfl
@[simp] theorem Reg.val_7 : ((7 : Reg) : Nat) = 7 := rfl
@[simp] theorem Reg.val_8 : ((8 : Reg) : Nat) = 8 := rfl
@[simp] theorem Reg.val_9 : ((9 : Reg) : Nat) = 9 := rfl
@[simp] theorem Reg.val_10 : ((10 : Reg) : Nat) = 10 := rfl
@[simp] theorem Reg.val_11 : ((11 : Reg) : Nat) = 11 := rfl
@[simp] theorem Reg.val_12 : ((12 : Reg) : Nat) = 12 := rfl
@[simp] theorem Reg.val_13 : ((13 : Reg) : Nat) = 13 := rfl
@[simp] theorem Reg.val_14 : ((14 : Reg) : Nat) = 14 := rfl
@[simp] theorem Reg.val_15 : ((15 : Reg) : Nat) = 15 := rfl
@[simp] theorem Reg.val_16 : ((16 : Reg) : Nat) = 16 := rfl
@[simp] theorem Reg.val_17 : ((17 : Reg) : Nat) = 17 := rfl
@[simp] theorem Reg.val_18 : ((18 : Reg) : Nat) = 18 := rfl
@[simp] theorem Reg.val_19 : ((19 : Reg) : Nat) = 19 := rfl
@[simp] theorem Reg.val_20 : ((20 : Reg) : Nat) = 20 := rfl
@[simp] theorem Reg.val_21 : ((21 : Reg) : Nat) = 21 := rfl
@[simp] theorem Reg.val_22 : ((22 : Reg) : Nat) = 22 := rfl
@[simp] theorem Reg.val_23 : ((23 : Reg) : Nat) = 23 := rfl
@[simp] theorem Reg.val_24 : ((24 : Reg) : Nat) = 24 := rfl
@[simp] theorem Reg.val_25 : ((25 : Reg) : Nat) = 25 := rfl
@[simp] theorem Reg.val_26 : ((26 : Reg) : Nat) = 26 := rfl
@[simp] theorem Reg.val_27 : ((27 : Reg) : Nat) = 27 := rfl
@[simp] theorem Reg.val_28 : ((28 : Reg) : Nat) = 28 := rfl
@[simp] theorem Reg.val_29 : ((29 : Reg) : Nat) = 29 := rfl
@[simp] theorem Reg.val_30 : ((30 : Reg) : Nat) = 30 := rfl
@[simp] theorem Reg.val_31 : ((31 : Reg) : Nat) = 31 := rfl

/-! ## `advance` — preserves all fields except `pc`. -/

@[simp] theorem advance_pc (s : State) : (advance s).pc = s.pc + 4 := rfl
@[simp] theorem advance_regs (s : State) : (advance s).regs = s.regs := rfl
@[simp] theorem advance_mem (s : State) : (advance s).mem = s.mem := rfl

/-! ## `jumpTo` — preserves all fields except `pc`. -/

@[simp] theorem jumpTo_pc (s : State) (t : UInt32) : (jumpTo s t).pc = t := rfl
@[simp] theorem jumpTo_regs (s : State) (t : UInt32) : (jumpTo s t).regs = s.regs := rfl
@[simp] theorem jumpTo_mem (s : State) (t : UInt32) : (jumpTo s t).mem = s.mem := rfl

@[simp] theorem getReg_jumpTo (s : State) (t : UInt32) (r : Reg) :
    getReg (jumpTo s t) r = getReg s r := by unfold getReg; rfl

/-! ## `setReg` — preserves all fields except `regs`. -/

@[simp] theorem setReg_pc (s : State) (r : Reg) (v : UInt32) : (setReg s r v).pc = s.pc := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_mem (s : State) (r : Reg) (v : UInt32) : (setReg s r v).mem = s.mem := by
  unfold setReg; split <;> rfl

/-- `setReg` to register 0 is a no-op (x0 is hardwired to 0). -/
@[simp] theorem setReg_zero (s : State) (v : UInt32) : setReg s 0 v = s := by
  unfold setReg; simp

/-! ## `getReg` / `setReg` interaction.  Side conditions are on the
`Fin 32` register indices; for concrete literal registers `decide`
discharges them automatically. -/

@[simp] theorem getReg_zero (s : State) : getReg s 0 = 0 := by unfold getReg; rfl

/-- Reading the just-written register (for r ≠ 0). -/
@[simp] theorem getReg_setReg_same (s : State) (r : Reg) (v : UInt32) (h : r ≠ 0) :
    getReg (setReg s r v) r = v := by
  unfold getReg setReg
  rw [if_neg h, if_neg h]
  show (s.regs.set r.val v r.isLt)[r.val] = v
  exact Vector.getElem_set_self _

/-- Reading a different register (frame). -/
@[simp] theorem getReg_setReg_other (s : State) (r r' : Reg) (v : UInt32)
    (h_ne : r ≠ r') (h0 : r' ≠ 0) :
    getReg (setReg s r v) r' = getReg s r' := by
  unfold getReg setReg
  rw [if_neg h0]
  split
  · rfl
  · show (s.regs.set r.val v r.isLt)[r'.val] = s.regs[r'.val]
    apply Vector.getElem_set_ne
    intro contra; exact h_ne (Fin.ext contra)

/-! ## Memory accessors only depend on `.mem`, which `advance`/`setReg`
preserve. -/

@[simp] theorem loadByte_advance (s : State) (a : UInt32) :
    loadByte (advance s) a = loadByte s a := rfl

@[simp] theorem loadByte_setReg (s : State) (r : Reg) (v a : UInt32) :
    loadByte (setReg s r v) a = loadByte s a := by unfold loadByte setReg; split <;> rfl

@[simp] theorem loadWord_advance (s : State) (a : UInt32) :
    loadWord (advance s) a = loadWord s a := by unfold loadWord; simp

@[simp] theorem loadWord_setReg (s : State) (r : Reg) (v a : UInt32) :
    loadWord (setReg s r v) a = loadWord s a := by unfold loadWord; simp

/-! ## `getReg` propagates through state updates that don't change regs. -/

@[simp] theorem getReg_advance (s : State) (r : Reg) :
    getReg (advance s) r = getReg s r := by unfold getReg; rfl

@[simp] theorem getReg_storeByte (s : State) (a : UInt32) (b : UInt8) (r : Reg) :
    getReg (storeByte s a b) r = getReg s r := by unfold getReg; rfl

@[simp] theorem getReg_storeWord (s : State) (a v : UInt32) (r : Reg) :
    getReg (storeWord s a v) r = getReg s r := by
  unfold storeWord; simp

/-! ## `storeByte` — preserves all fields except `mem`. -/

@[simp] theorem storeByte_pc (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).pc = s.pc := rfl
@[simp] theorem storeByte_regs (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).regs = s.regs := rfl

/-! ## `storeWord` — preserves all fields except `mem`. -/

@[simp] theorem storeWord_pc (s : State) (a v : UInt32) :
    (storeWord s a v).pc = s.pc := by unfold storeWord; simp
@[simp] theorem storeWord_regs (s : State) (a v : UInt32) :
    (storeWord s a v).regs = s.regs := by unfold storeWord; simp

end MemcpyProof.Hoare
