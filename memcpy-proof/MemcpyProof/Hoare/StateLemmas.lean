/-
Field-projection simp lemmas for `setReg`, `advance`, `storeByte`,
`storeWord`, `loadWord`, etc.  These are the workhorses for reducing
the post-state of a chain of `exec` applications to explicit values.

`Regs` is `Vector UInt32 32`, register operands are `Reg := Fin 32`,
register lookups go via `s.regs[r.val]`.
-/

import MemcpyProof.Sem
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Coercion `(n : Reg) → Nat` evaluates for literals.

Each of the 32 register indices has its own `@[simp]` lemma saying
`((n : Reg) : Nat) = n`.  This lets simp peel `Vector.set/getElem`
side conditions like `(↑(11 : Reg) : Nat) ≠ r.val` down to
`(11 : Nat) ≠ r.val`, which matches `Fin 32`-quantified frame
hypotheses directly. -/

@[simp, grind =] theorem Reg.val_0 : ((0 : Reg) : Nat) = 0 := rfl
@[simp, grind =] theorem Reg.val_1 : ((1 : Reg) : Nat) = 1 := rfl
@[simp, grind =] theorem Reg.val_2 : ((2 : Reg) : Nat) = 2 := rfl
@[simp, grind =] theorem Reg.val_3 : ((3 : Reg) : Nat) = 3 := rfl
@[simp, grind =] theorem Reg.val_4 : ((4 : Reg) : Nat) = 4 := rfl
@[simp, grind =] theorem Reg.val_5 : ((5 : Reg) : Nat) = 5 := rfl
@[simp, grind =] theorem Reg.val_6 : ((6 : Reg) : Nat) = 6 := rfl
@[simp, grind =] theorem Reg.val_7 : ((7 : Reg) : Nat) = 7 := rfl
@[simp, grind =] theorem Reg.val_8 : ((8 : Reg) : Nat) = 8 := rfl
@[simp, grind =] theorem Reg.val_9 : ((9 : Reg) : Nat) = 9 := rfl
@[simp, grind =] theorem Reg.val_10 : ((10 : Reg) : Nat) = 10 := rfl
@[simp, grind =] theorem Reg.val_11 : ((11 : Reg) : Nat) = 11 := rfl
@[simp, grind =] theorem Reg.val_12 : ((12 : Reg) : Nat) = 12 := rfl
@[simp, grind =] theorem Reg.val_13 : ((13 : Reg) : Nat) = 13 := rfl
@[simp, grind =] theorem Reg.val_14 : ((14 : Reg) : Nat) = 14 := rfl
@[simp, grind =] theorem Reg.val_15 : ((15 : Reg) : Nat) = 15 := rfl
@[simp, grind =] theorem Reg.val_16 : ((16 : Reg) : Nat) = 16 := rfl
@[simp, grind =] theorem Reg.val_17 : ((17 : Reg) : Nat) = 17 := rfl
@[simp, grind =] theorem Reg.val_18 : ((18 : Reg) : Nat) = 18 := rfl
@[simp, grind =] theorem Reg.val_19 : ((19 : Reg) : Nat) = 19 := rfl
@[simp, grind =] theorem Reg.val_20 : ((20 : Reg) : Nat) = 20 := rfl
@[simp, grind =] theorem Reg.val_21 : ((21 : Reg) : Nat) = 21 := rfl
@[simp, grind =] theorem Reg.val_22 : ((22 : Reg) : Nat) = 22 := rfl
@[simp, grind =] theorem Reg.val_23 : ((23 : Reg) : Nat) = 23 := rfl
@[simp, grind =] theorem Reg.val_24 : ((24 : Reg) : Nat) = 24 := rfl
@[simp, grind =] theorem Reg.val_25 : ((25 : Reg) : Nat) = 25 := rfl
@[simp, grind =] theorem Reg.val_26 : ((26 : Reg) : Nat) = 26 := rfl
@[simp, grind =] theorem Reg.val_27 : ((27 : Reg) : Nat) = 27 := rfl
@[simp, grind =] theorem Reg.val_28 : ((28 : Reg) : Nat) = 28 := rfl
@[simp, grind =] theorem Reg.val_29 : ((29 : Reg) : Nat) = 29 := rfl
@[simp, grind =] theorem Reg.val_30 : ((30 : Reg) : Nat) = 30 := rfl
@[simp, grind =] theorem Reg.val_31 : ((31 : Reg) : Nat) = 31 := rfl

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
    (h_ne : r ≠ r') :
    getReg (setReg s r v) r' = getReg s r' := by
  unfold getReg setReg
  grind

@[simp] theorem getReg_setReg_other_val {s : State} {r r' : Reg} {v : UInt32}
    (h_ne : r'.val ≠ r.val) :
    getReg (setReg s r v) r' = getReg s r' := by
  unfold getReg setReg
  grind

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

/-- Reading from `(storeByte s a v).mem` at the stored address gives `v`. -/
@[simp] theorem storeByte_mem_same (s : State) (a : UInt32) (b : UInt8) :
    (storeByte s a b).mem a = b := by
  show (if a == a then b else s.mem a) = b
  simp

/-- Reading from `(storeByte s a v).mem` at a different address is untouched. -/
theorem storeByte_mem_other (s : State) (a a' : UInt32) (b : UInt8) (h : a' ≠ a) :
    (storeByte s a b).mem a' = s.mem a' := by
  show (if a' == a then b else s.mem a') = s.mem a'
  have heq : (a' == a) = false := by simp [h]
  rw [heq]; simp

/-- `loadByte` after `storeByte` — case-split form. -/
@[simp] theorem loadByte_storeByte_same (s : State) (a : UInt32) (b : UInt8) :
    loadByte (storeByte s a b) a = b := storeByte_mem_same s a b

theorem loadByte_storeByte_other (s : State) (a a' : UInt32) (b : UInt8) (h : a' ≠ a) :
    loadByte (storeByte s a b) a' = loadByte s a' := storeByte_mem_other s a a' b h

/-! ## Byte ↔ word view translation.

Memory is byte-indexed (`mem : UInt32 → UInt8`).  Word reads/writes
decompose into 4 byte ops.  These lemmas let proofs cross the
byte/word boundary cheaply. -/

/-- A word load equals another word load iff all four constituent
    bytes agree.  Useful when a block's byte-level mem fact needs to
    feed a word-level downstream block. -/
theorem loadWord_eq_of_bytes_eq (s s' : State) (a b : UInt32)
    (h0 : s'.mem a = s.mem b)
    (h1 : s'.mem (a + 1) = s.mem (b + 1))
    (h2 : s'.mem (a + 2) = s.mem (b + 2))
    (h3 : s'.mem (a + 3) = s.mem (b + 3)) :
    loadWord s' a = loadWord s b := by
  unfold loadWord loadByte
  rw [h0, h1, h2, h3]

/-- Each byte of a `storeWord`'s effect, by offset. -/
theorem storeWord_mem_byte (s : State) (a v : UInt32) (i : UInt32) (h : i < 4) :
    (storeWord s a v).mem (a + i) = (v >>> (i * 8)).toUInt8 := by
  unfold storeWord
  -- Storing 4 bytes at a, a+1, a+2, a+3.  Each byte i gets v >>> (i*8).
  -- Need to case-split on i ∈ {0,1,2,3}.
  -- The store-byte chain ends with `a+3 ← (v >>> 24).toUInt8`.
  rcases (by bv_decide : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · -- i = 0
    rw [show a + 0 = a from by bv_decide,
        show (0 : UInt32) * 8 = 0 from by bv_decide]
    rw [storeByte_mem_other _ _ _ _ (by bv_decide)]
    rw [storeByte_mem_other _ _ _ _ (by bv_decide)]
    rw [storeByte_mem_other _ _ _ _ (by bv_decide)]
    rw [storeByte_mem_same]
    show v.toUInt8 = (v >>> 0).toUInt8
    bv_decide
  · rw [show (1 : UInt32) * 8 = 8 from by bv_decide]
    rw [storeByte_mem_other _ _ _ _ (by bv_decide)]
    rw [storeByte_mem_other _ _ _ _ (by bv_decide)]
    rw [storeByte_mem_same]
  · rw [show (2 : UInt32) * 8 = 16 from by bv_decide]
    rw [storeByte_mem_other _ _ _ _ (by bv_decide)]
    rw [storeByte_mem_same]
  · rw [show (3 : UInt32) * 8 = 24 from by bv_decide]
    rw [storeByte_mem_same]

/-- Reading a byte outside `[a, a+4)` after a `storeWord` is unchanged. -/
theorem storeWord_mem_other (s : State) (a v a' : UInt32)
    (h0 : a' ≠ a) (h1 : a' ≠ a + 1) (h2 : a' ≠ a + 2) (h3 : a' ≠ a + 3) :
    (storeWord s a v).mem a' = s.mem a' := by
  unfold storeWord
  rw [storeByte_mem_other _ _ _ _ h3]
  rw [storeByte_mem_other _ _ _ _ h2]
  rw [storeByte_mem_other _ _ _ _ h1]
  rw [storeByte_mem_other _ _ _ _ h0]

/-! ## `signExt` lemmas. -/

/-- Sign-extending a UInt8 (via `.toUInt32`, signBit = 7) then truncating
    back to UInt8 is the identity.  The sign extension only sets bits
    8–31; the low 8 bits are preserved, and `.toUInt8` returns them. -/
@[simp, grind =] theorem signExt_byte_toUInt8 (b : UInt8) :
    (signExt b.toUInt32 7).toUInt8 = b := by
  show ((b.toUInt32 ^^^ (1 <<< (7 : UInt32))) - (1 <<< (7 : UInt32))).toUInt8 = b
  bv_decide

@[simp, grind =] theorem signExt_UInt8_toUInt8 (b : UInt8) :
  (b ^^^ (1 <<< (7 : UInt8))) - (1 <<< (7 : UInt8)) = b := by
  bv_decide

/-! ## `storeWord` — preserves all fields except `mem`. -/

@[simp] theorem storeWord_pc (s : State) (a v : UInt32) :
    (storeWord s a v).pc = s.pc := by unfold storeWord; simp
@[simp] theorem storeWord_regs (s : State) (a v : UInt32) :
    (storeWord s a v).regs = s.regs := by unfold storeWord; simp

end MemcpyProof.Hoare
