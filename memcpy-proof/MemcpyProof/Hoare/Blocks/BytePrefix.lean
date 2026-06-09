/-
B2 — the byte-prefix loop body (PCs 0x20090c..0x200940, 14 instr).

Copies one byte from `[a1]` to `[a0]` and advances pointers, then
computes in `a7` the loop-continuation predicate
`((a1+1) & 3 ≠ 0) ∧ (a2-1 ≠ 0)`.

Block layout (1-based step indices):

   1. addi a5, a1, 1      -- a5 ← a1 + 1   (probe pointer for align test)
   2. addi a6, a0, 0      -- a6 ← a0
   3. lb   a7, 0(a1)      -- a7 ← signExt(Mem[a1])
   4. addi a4, a1, 1      -- a4 ← a1 + 1   (saved next-a1)
   5. addi a3, a6, 1      -- a3 ← a0 + 1   (saved next-a0)
   6. sb   a7, 0(a6)      -- Mem[a0] ← (a7 as UInt8)
   7. addi a2, a2, -1     -- a2 ← a2 - 1
   8. andi a1, a5, 3      -- a1 ← (a1+1) & 3
   9. sltu a1, zero, a1   -- a1 ← (0 < a1)  ? 1 : 0
  10. sltu a6, zero, a2   -- a6 ← (0 < a2)  ? 1 : 0
  11. and  a7, a1, a6     -- a7 ← a1 & a6  (= "loop again" flag)
  12. addi a5, a5, 1      -- a5 ← a1 + 2
  13. addi a1, a4, 0      -- a1 ← a1 + 1
  14. addi a6, a3, 0      -- a6 ← a0 + 1

Split into 5 / 5 / 4 chunks.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ### `loop_setup`: the first 2 instrs of B2.

These run once, before the byte-prefix loop body proper.  The bne at
the end of the loop branches back to *after* these two instrs, so the
setup is *not* re-executed on subsequent iterations. -/

def loop_setup : List Instr :=
  [ Instr.addi 15 11 1
  , Instr.addi 16 10 0
  ]

def loop_setup_triple_composed :=
  (Triple_addi 15 11 1).append <|
  (Triple_addi 16 10 0)

/-- Post-condition of `loop_setup`: `a5 ← a1 + 1, a6 ← a0`. -/
def R_loop_setup : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 8 ∧
    getReg s' 15 = getReg s 11 + 1 ∧
    getReg s' 16 = getReg s 10 ∧
    (∀ r : Fin 32, r.val ≠ 15 → r.val ≠ 16 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

theorem loop_setup_triple :
    Triple loop_setup R_loop_setup := by
  refine Triple.weaken loop_setup_triple_composed ?_
  rintro s s' ⟨_, rfl, rfl⟩
  grind [R_loop_setup]

/-! ### `loop_copy_byte`: load + store one byte, plus pointer scratch.

  Four instructions:
    lb   a7, 0(a1)       -- a7 ← signExt(Mem[a1])
    addi a4, a1, 1       -- a4 ← a1 + 1     (saved next-a1)
    addi a3, a6, 1       -- a3 ← a6 + 1     (saved next-dst)
    sb   a7, 0(a6)       -- Mem[a6] ← a7 (as UInt8)

  Net effect: one byte copied from `[a1]` to `[a6]`; a3, a4, a7 set. -/

def loop_copy_byte : List Instr :=
  [ Instr.lb   17 11 0
  , Instr.addi 14 11 1
  , Instr.addi 13 16 1
  , Instr.sb   16 17 0
  ]

def loop_copy_byte_triple_composed :=
  (Triple_lb   17 11 0).append <|
  (Triple_addi 14 11 1).append <|
  (Triple_addi 13 16 1).append <|
  (Triple_sb   16 17 0)

/-- Post-condition of `loop_copy_byte`: one byte copied from `[a1]` to
    `[a6]`; pointer-scratch `a3, a4` set; `a7` holds the sign-extended
    byte.  Other regs and memory bytes preserved.

    Memory effect uses `loadByte s a1` (the raw byte) directly — the
    proof needs `signExt_byte_toUInt8` to bridge from the chain's
    `(signExt _).toUInt8` form. -/
def R_loop_copy_byte : State → State → Prop :=
  fun s s' =>
    let a1 := getReg s 11
    let a6 := getReg s 16
    s'.pc = s.pc + 16 ∧
    getReg s' 13 = a6 + 1 ∧
    getReg s' 14 = a1 + 1 ∧
    getReg s' 17 = signExt (loadByte s a1).toUInt32 7 ∧
    (∀ r : Fin 32, r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s a6 (loadByte s a1)).mem

theorem loop_copy_byte_triple :
    Triple loop_copy_byte R_loop_copy_byte := by
  refine Triple.weaken loop_copy_byte_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  simp
  grind [R_loop_copy_byte]

/-! ### `loop_predicate`: decrement count + compute the loop-continue flag.

  Five instructions:
    addi a2, a2, -1       -- a2 ← a2 - 1
    andi a1, a5, 3        -- a1 ← (a5) & 3      (a5 = entry-a1 + 1)
    sltu a1, zero, a1     -- a1 ← (a5 & 3 ≠ 0) ? 1 : 0
    sltu a6, zero, a2     -- a6 ← (a2 - 1 ≠ 0)  ? 1 : 0
    and  a7, a1, a6       -- a7 ← a1 & a6  ("continue" flag)

  No memory effect.  Reads `a5` and `a2`, writes `a1, a2, a6, a7`. -/

def loop_predicate : List Instr :=
  [ Instr.addi 12 12 0xFFFFFFFF
  , Instr.andi 11 15 3
  , Instr.sltu 11 0 11
  , Instr.sltu 16 0 12
  , Instr.and_ 17 11 16
  ]

def loop_predicate_triple_composed :=
  (Triple_addi 12 12 0xFFFFFFFF).append <|
  (Triple_andi 11 15 3).append <|
  (Triple_sltu 11 0 11).append <|
  (Triple_sltu 16 0 12).append <|
  (Triple_and  17 11 16)

/-- Post-condition of `loop_predicate`. -/
def R_loop_predicate : State → State → Prop :=
  fun s s' =>
    let a2' : UInt32 := getReg s 12 - 1
    let a1_tst : Bool := (getReg s 15 &&& 3) != 0
    let a2_tst : Bool := a2' != 0
    s'.pc = s.pc + 20 ∧
    getReg s' 11 = a1_tst.toUInt32 ∧
    getReg s' 12 = a2' ∧
    getReg s' 16 = a2_tst.toUInt32 ∧
    getReg s' 17 = (a1_tst && (getReg s' 12) != 0).toUInt32 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

theorem loop_predicate_triple :
    Triple loop_predicate R_loop_predicate := by
  refine Triple.weaken loop_predicate_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  have sub_eq_add (x : UInt32) : x - 1 = x + 0xFFFFFFFF := by bv_decide
  have zero_lt_eq_neq_zero (x : UInt32) : (0 < x) = (x != 0) := by grind
  simp [R_loop_predicate, h_pc, Bool.toUInt32, sub_eq_add, zero_lt_eq_neq_zero]
  refine ⟨?_, ?_⟩
  · generalize h11 : getReg s 15 = a15
    bv_decide
  · intro r h11 h12 h16 h17
    simp [setReg, Ne.symm h11, Ne.symm h12, Ne.symm h16, Ne.symm h17]

/-! ### `loop_branch`: final pointer bumps + the back-branch.

  Four instructions:
    addi a5, a5, 1     -- a5 ← a5 + 1   (= a1+2 by the loop invariant)
    addi a1, a4, 0     -- a1 ← a4       (= advance src pointer for next iter)
    addi a6, a3, 0     -- a6 ← a3       (= advance dst pointer for next iter)
    bne  a7, zero, -48 -- loop back if `a7 ≠ 0`, else fall through

  The bne target lands at the *3rd* instruction of B2 (skipping the 2-instr
  setup), so this block's "branch taken" pc is `s.pc + 12 + (-48) = s.pc - 36`.
  Fall-through: `s.pc + 16`. -/

def loop_branch : List Instr :=
  [ Instr.addi 15 15 1
  , Instr.addi 11 14 0
  , Instr.addi 16 13 0
  , Instr.bne  17 0 0xFFFFFFD0
  ]

def loop_branch_triple_composed :=
  (Triple_addi 15 15 1).append <|
  (Triple_addi 11 14 0).append <|
  (Triple_addi 16 13 0).append <|
  (Triple_bne  17 0 0xFFFFFFD0)

/-- Post-condition of `loop_branch`.

  Pointer bumps land in `a5, a1, a6`; pc dispatches on whether `a7 ≠ 0`.
  No memory effect. -/
def R_loop_branch : State → State → Prop :=
  fun s s' =>
    let taken : Bool := getReg s 17 != 0
    s'.pc = (if taken then s.pc - 36 else s.pc + 16) ∧
    getReg s' 11 = getReg s 14 ∧
    getReg s' 15 = getReg s 15 + 1 ∧
    getReg s' 16 = getReg s 13 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 15 → r.val ≠ 16 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

theorem loop_branch_triple :
    Triple loop_branch R_loop_branch := by
  refine Triple.weaken loop_branch_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  by_cases h : getReg s 17 = 0
  · simp [R_loop_branch, h]
    grind
  · simp [R_loop_branch, h]
    grind


end MemcpyProof.Hoare
