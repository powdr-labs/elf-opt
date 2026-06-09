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

/-! ## Chunk 1 (5 instr): byte-load + address-setup. -/

private def bp_c1 : List Instr :=
  [ Instr.addi 15 11 1
  , Instr.addi 16 10 0
  , Instr.lb   17 11 0
  , Instr.addi 14 11 1
  , Instr.addi 13 16 1
  ]

private def R_bp_c1 : State → State → Prop :=
  fun s s' =>
    let a0 := getReg s 10
    let a1 := getReg s 11
    s'.pc = s.pc + 20 ∧
    getReg s' 13 = a0 + 1 ∧
    getReg s' 14 = a1 + 1 ∧
    getReg s' 15 = a1 + 1 ∧
    getReg s' 16 = a0 ∧
    getReg s' 17 = signExt (loadByte s a1).toUInt32 7 ∧
    (∀ r : Fin 32, r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 15 → r.val ≠ 16 →
       r.val ≠ 17 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem bp_c1_triple : Triple bp_c1 R_bp_c1 := by
  have h := ((Triple_addi 15 11 1).append <|
             (Triple_addi 16 10 0).append <|
             (Triple_lb   17 11 0).append <|
             (Triple_addi 14 11 1).append <|
             (Triple_addi 13 16 1))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_bp_c1, h_pc]
  intro r h13 h14 h15 h16 h17
  simp [setReg, Ne.symm h13, Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17]

/-! ## Chunk 2 (5 instr): byte-store + loop-predicate parts. -/

private def bp_c2 : List Instr :=
  [ Instr.sb   16 17 0
  , Instr.addi 12 12 0xFFFFFFFF
  , Instr.andi 11 15 3
  , Instr.sltu 11 0 11
  , Instr.sltu 16 0 12
  ]

private def R_bp_c2 : State → State → Prop :=
  fun s s' =>
    let a2' := getReg s 12 + 0xFFFFFFFF
    s'.pc = s.pc + 20 ∧
    getReg s' 11 = (if 0 < (getReg s 15 &&& 3) then 1 else 0) ∧
    getReg s' 12 = a2' ∧
    getReg s' 16 = (if 0 < a2' then 1 else 0) ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 16 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s (getReg s 16) (getReg s 17).toUInt8).mem

private theorem bp_c2_triple : Triple bp_c2 R_bp_c2 := by
  have h := ((Triple_sb   16 17 0).append <|
             (Triple_addi 12 12 0xFFFFFFFF).append <|
             (Triple_andi 11 15 3).append <|
             (Triple_sltu 11 0 11).append <|
             (Triple_sltu 16 0 12))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_bp_c2, h_pc]
  intro r h11 h12 h16
  simp [setReg, Ne.symm h11, Ne.symm h12, Ne.symm h16]

/-! ## Chunk 3 (4 instr): bitwise-and the two predicate bits + pointer bumps. -/

private def bp_c3 : List Instr :=
  [ Instr.and_ 17 11 16
  , Instr.addi 15 15 1
  , Instr.addi 11 14 0
  , Instr.addi 16 13 0
  ]

private def R_bp_c3 : State → State → Prop :=
  fun s s' =>
    s'.pc = s.pc + 16 ∧
    getReg s' 11 = getReg s 14 ∧
    getReg s' 15 = getReg s 15 + 1 ∧
    getReg s' 16 = getReg s 13 ∧
    getReg s' 17 = getReg s 11 &&& getReg s 16 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem bp_c3_triple : Triple bp_c3 R_bp_c3 := by
  have h := ((Triple_and  17 11 16).append <|
             (Triple_addi 15 15 1).append <|
             (Triple_addi 11 14 0).append <|
             (Triple_addi 16 13 0))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 = s.pc + 16 := by bv_decide
  simp [R_bp_c3, h_pc]
  intro r h11 h15 h16 h17
  simp [setReg, Ne.symm h11, Ne.symm h15, Ne.symm h16, Ne.symm h17]

/-! ## The full block — `Triple.append` of the 3 chunks. -/

def block_byte_prefix_body : List Instr := bp_c1 ++ bp_c2 ++ bp_c3

theorem block_byte_prefix_body_triple_composed :
    Triple block_byte_prefix_body
      (RComp R_bp_c1 (RComp R_bp_c2 R_bp_c3)) := by
  have h := (bp_c1_triple.append bp_c2_triple).append bp_c3_triple
  refine Triple.weaken h ?_
  -- left-associated `RComp (RComp R_c1 R_c2) R_c3` → right-associated.
  rintro s s' ⟨t2, ⟨t1, h1, h2⟩, h3⟩
  exact ⟨t1, h1, t2, h2, h3⟩

/-! ## Flat structured post-condition.

After running all 14 instructions of `block_byte_prefix_body`:
* `Mem[a0]` ← `signExt(Mem[a1]).toUInt8`         (one byte copied)
* `a1 ← a1 + 1`, `a6 ← a0 + 1`                   (pointers advanced)
* `a2 ← a2 - 1`                                  (count decremented)
* `a5 ← a1 + 2`, `a4 ← a1 + 1`, `a3 ← a0 + 1`    (scratch)
* `a7 ← a7_fin` := `(a1+1) & 3 ≠ 0 ? 1 : 0` ∧ `a2-1 ≠ 0 ? 1 : 0`
* `pc ← s.pc + 56` -/
def R_block_byte_prefix_body : State → State → Prop :=
  fun s s' =>
    let a0 := getReg s 10
    let a1 := getReg s 11
    let a2 := getReg s 12
    let ext : UInt32 := signExt (loadByte s a1).toUInt32 7
    let a2' : UInt32 := a2 + 0xFFFFFFFF
    let a1_tst : UInt32 := if 0 < ((a1 + 1) &&& 3) then 1 else 0
    let a2_tst : UInt32 := if 0 < a2' then 1 else 0
    let a7_fin : UInt32 := a1_tst &&& a2_tst
    s'.pc = s.pc + 56 ∧
    getReg s' 11 = a1 + 1 ∧
    getReg s' 12 = a2' ∧
    getReg s' 13 = a0 + 1 ∧
    getReg s' 14 = a1 + 1 ∧
    getReg s' 15 = a1 + 2 ∧
    getReg s' 16 = a0 + 1 ∧
    getReg s' 17 = a7_fin ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
       r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s a0 ext.toUInt8).mem

/-- Helper: turn an `.regs[r.val] = .regs[r.val]` frame fact into a
    `getReg X r = getReg Y r` fact, for any non-zero literal register. -/
private theorem getReg_eq_of_regs_eq {s₁ s₂ : State} {r : Reg} (h0 : r ≠ 0)
    (h : s₁.regs[r.val] = s₂.regs[r.val]) :
    getReg s₁ r = getReg s₂ r := by
  unfold getReg; rw [if_neg h0, if_neg h0]; exact h

theorem block_byte_prefix_body_triple :
    Triple block_byte_prefix_body R_block_byte_prefix_body := by
  refine Triple.weaken block_byte_prefix_body_triple_composed ?_
  rintro s s' ⟨t1, h1, t2, h2, h3⟩
  simp only [R_bp_c1] at h1
  simp only [R_bp_c2] at h2
  simp only [R_bp_c3] at h3
  obtain ⟨h1_pc, h1_13, h1_14, h1_15, h1_16, h1_17, h1_frame, h1_mem⟩ := h1
  obtain ⟨h2_pc, h2_11, h2_12, h2_16, h2_frame, h2_mem⟩ := h2
  obtain ⟨h3_pc, h3_11, h3_15, h3_16, h3_17, h3_frame, h3_mem⟩ := h3
  -- Lift frame conditions from `regs[r.val]` form to `getReg` form for the
  -- specific registers we'll need.
  have h2_t1_14 : getReg t2 14 = getReg t1 14 :=
    getReg_eq_of_regs_eq (by decide)
      (h2_frame ⟨14, by decide⟩ (by decide) (by decide) (by decide))
  have h2_t1_13 : getReg t2 13 = getReg t1 13 :=
    getReg_eq_of_regs_eq (by decide)
      (h2_frame ⟨13, by decide⟩ (by decide) (by decide) (by decide))
  have h2_t1_15 : getReg t2 15 = getReg t1 15 :=
    getReg_eq_of_regs_eq (by decide)
      (h2_frame ⟨15, by decide⟩ (by decide) (by decide) (by decide))
  have h3_t2_12 : getReg s' 12 = getReg t2 12 :=
    getReg_eq_of_regs_eq (by decide)
      (h3_frame ⟨12, by decide⟩ (by decide) (by decide) (by decide) (by decide))
  have h3_t2_13 : getReg s' 13 = getReg t2 13 :=
    getReg_eq_of_regs_eq (by decide)
      (h3_frame ⟨13, by decide⟩ (by decide) (by decide) (by decide) (by decide))
  have h3_t2_14 : getReg s' 14 = getReg t2 14 :=
    getReg_eq_of_regs_eq (by decide)
      (h3_frame ⟨14, by decide⟩ (by decide) (by decide) (by decide) (by decide))
  have h1_t1_12 : getReg t1 12 = getReg s 12 :=
    getReg_eq_of_regs_eq (by decide)
      (h1_frame ⟨12, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide))
  simp only [R_block_byte_prefix_body]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pc = s.pc + 56
    rw [h3_pc, h2_pc, h1_pc]; bv_decide
  · -- a1 = a1 + 1
    rw [h3_11, h2_t1_14, h1_14]
  · -- a2 = a2 - 1
    rw [h3_t2_12, h2_12, h1_t1_12]
  · -- a3 = a0 + 1
    rw [h3_t2_13, h2_t1_13, h1_13]
  · -- a4 = a1 + 1
    rw [h3_t2_14, h2_t1_14, h1_14]
  · -- a5 = a1 + 2
    rw [h3_15, h2_t1_15, h1_15]; bv_decide
  · -- a6 = a0 + 1
    rw [h3_16, h2_t1_13, h1_13]
  · -- a7 = a7_fin
    rw [h3_17, h2_11, h2_16, h1_15, h1_t1_12]
  · -- frame
    intro r hr11 hr12 hr13 hr14 hr15 hr16 hr17
    rw [h3_frame r hr11 hr15 hr16 hr17,
        h2_frame r hr11 hr12 hr16,
        h1_frame r hr13 hr14 hr15 hr16 hr17]
  · -- mem
    rw [h3_mem, h2_mem, h1_16, h1_17]
    unfold storeByte
    simp [h1_mem]

/-! ## Loop-aware split of `block_byte_prefix_body`.

The bne at the end of the loop has offset `0xFFFFFFD0 = -48` from its own
PC.  The bne is at byte-offset 56 in the loop, so the branch lands at
byte-offset 8 — i.e., **instruction 2** of `block_byte_prefix_body`,
skipping the first two `addi`s.

Therefore the loop's actual execution is:
  * **First iteration**: instrs 0..13 (the full body) + bne.
  * **Subsequent iterations**: instrs 2..13 (skipping setup) + bne.

Below we split `block_byte_prefix_body` into:
  * `block_byte_prefix_setup` — the 2 instrs that run only once.
  * `block_byte_prefix_main`  — the 12 instrs that run every iteration.

For the loop's full semantics, the structure is
`setup ++ (main ++ bne) ^ K`.
-/

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


/-! ### Main-body chunk: the 12 instrs that run every loop iteration.

The post-condition is parametric in **entry**'s `x15` and `x16`: the loop
maintains the invariant `x15 = a1 + 1, x16 = current dst pointer`, but
that's a property of the loop, not of the main body alone. -/

private def bp_c1_rest : List Instr :=
  [ Instr.lb   17 11 0
  , Instr.addi 14 11 1
  , Instr.addi 13 16 1
  ]

private def R_bp_c1_rest : State → State → Prop :=
  fun s s' =>
    let a1 := getReg s 11
    let x16_in := getReg s 16
    s'.pc = s.pc + 12 ∧
    getReg s' 13 = x16_in + 1 ∧
    getReg s' 14 = a1 + 1 ∧
    getReg s' 17 = signExt (loadByte s a1).toUInt32 7 ∧
    (∀ r : Fin 32, r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

private theorem bp_c1_rest_triple : Triple bp_c1_rest R_bp_c1_rest := by
  have h := ((Triple_lb   17 11 0).append <|
             (Triple_addi 14 11 1).append <|
             (Triple_addi 13 16 1))
  refine Triple.weaken h ?_
  rintro s s' ⟨_, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 = s.pc + 12 := by bv_decide
  simp [R_bp_c1_rest, h_pc]
  intro r h13 h14 h17
  simp [setReg, Ne.symm h13, Ne.symm h14, Ne.symm h17]

def block_byte_prefix_main : List Instr := bp_c1_rest ++ bp_c2 ++ bp_c3

/-- Post-condition of `block_byte_prefix_main` (12 instrs).
    Parametric in entry's `x15` and `x16` (the loop invariant
    instantiates them to `a1 + 1` and the current dst pointer). -/
def R_block_byte_prefix_main : State → State → Prop :=
  fun s s' =>
    let a1 := getReg s 11
    let a2 := getReg s 12
    let x15_in := getReg s 15
    let x16_in := getReg s 16
    let a2' : UInt32 := a2 + 0xFFFFFFFF
    let a1_tst : UInt32 := if 0 < (x15_in &&& 3) then 1 else 0
    let a2_tst : UInt32 := if 0 < a2' then 1 else 0
    let a7_fin : UInt32 := a1_tst &&& a2_tst
    s'.pc = s.pc + 48 ∧
    getReg s' 11 = a1 + 1 ∧
    getReg s' 12 = a2' ∧
    getReg s' 13 = x16_in + 1 ∧
    getReg s' 14 = a1 + 1 ∧
    getReg s' 15 = x15_in + 1 ∧
    getReg s' 16 = x16_in + 1 ∧
    getReg s' 17 = a7_fin ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
       r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte s x16_in (s.mem a1)).mem

theorem block_byte_prefix_main_triple :
    Triple block_byte_prefix_main R_block_byte_prefix_main := by
  -- Compose bp_c1_rest + bp_c2 + bp_c3.
  have h := (bp_c1_rest_triple.append bp_c2_triple).append bp_c3_triple
  refine Triple.weaken h ?_
  rintro s s' ⟨t2, ⟨t1, h1, h2⟩, h3⟩
  simp only [R_bp_c1_rest] at h1
  simp only [R_bp_c2] at h2
  simp only [R_bp_c3] at h3
  obtain ⟨h1_pc, h1_13, h1_14, h1_17, h1_frame, h1_mem⟩ := h1
  obtain ⟨h2_pc, h2_11, h2_12, h2_16, h2_frame, h2_mem⟩ := h2
  obtain ⟨h3_pc, h3_11, h3_15, h3_16, h3_17, h3_frame, h3_mem⟩ := h3
  -- Lift frame conditions.
  have h2_t1_14 : getReg t2 14 = getReg t1 14 :=
    getReg_eq_of_regs_eq (by decide)
      (h2_frame ⟨14, by decide⟩ (by decide) (by decide) (by decide))
  have h2_t1_13 : getReg t2 13 = getReg t1 13 :=
    getReg_eq_of_regs_eq (by decide)
      (h2_frame ⟨13, by decide⟩ (by decide) (by decide) (by decide))
  have h2_t1_15 : getReg t2 15 = getReg t1 15 :=
    getReg_eq_of_regs_eq (by decide)
      (h2_frame ⟨15, by decide⟩ (by decide) (by decide) (by decide))
  have h3_t2_12 : getReg s' 12 = getReg t2 12 :=
    getReg_eq_of_regs_eq (by decide)
      (h3_frame ⟨12, by decide⟩ (by decide) (by decide) (by decide) (by decide))
  have h3_t2_13 : getReg s' 13 = getReg t2 13 :=
    getReg_eq_of_regs_eq (by decide)
      (h3_frame ⟨13, by decide⟩ (by decide) (by decide) (by decide) (by decide))
  have h3_t2_14 : getReg s' 14 = getReg t2 14 :=
    getReg_eq_of_regs_eq (by decide)
      (h3_frame ⟨14, by decide⟩ (by decide) (by decide) (by decide) (by decide))
  -- Frame helpers for bp_c1_rest preserving x11, x12, x15, x16.
  have h1_t1_11 : getReg t1 11 = getReg s 11 :=
    getReg_eq_of_regs_eq (by decide)
      (h1_frame ⟨11, by decide⟩ (by decide) (by decide) (by decide))
  have h1_t1_12 : getReg t1 12 = getReg s 12 :=
    getReg_eq_of_regs_eq (by decide)
      (h1_frame ⟨12, by decide⟩ (by decide) (by decide) (by decide))
  have h1_t1_15 : getReg t1 15 = getReg s 15 :=
    getReg_eq_of_regs_eq (by decide)
      (h1_frame ⟨15, by decide⟩ (by decide) (by decide) (by decide))
  have h1_t1_16 : getReg t1 16 = getReg s 16 :=
    getReg_eq_of_regs_eq (by decide)
      (h1_frame ⟨16, by decide⟩ (by decide) (by decide) (by decide))
  simp only [R_block_byte_prefix_main]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pc = s.pc + 48
    rw [h3_pc, h2_pc, h1_pc]; bv_decide
  · -- a1 = a1 + 1 (from x14, set in bp_c1_rest, passed through)
    rw [h3_11, h2_t1_14, h1_14]
  · -- a2 = a2 - 1
    rw [h3_t2_12, h2_12, h1_t1_12]
  · -- a3 = x16_in + 1
    rw [h3_t2_13, h2_t1_13, h1_13]
  · -- a4 = a1 + 1
    rw [h3_t2_14, h2_t1_14, h1_14]
  · -- a5 = x15_in + 1
    rw [h3_15, h2_t1_15, h1_t1_15]
  · -- a6 = x16_in + 1 (from x13 in bp_c3)
    rw [h3_16, h2_t1_13, h1_13]
  · -- a7 = a7_fin
    rw [h3_17, h2_11, h2_16, h1_t1_15, h1_t1_12]
  · -- frame
    intro r hr11 hr12 hr13 hr14 hr15 hr16 hr17
    rw [h3_frame r hr11 hr15 hr16 hr17,
        h2_frame r hr11 hr12 hr16,
        h1_frame r hr13 hr14 hr17]
  · -- mem
    rw [h3_mem, h2_mem]
    rw [h1_t1_16, h1_17, signExt_byte_toUInt8]
    unfold storeByte loadByte
    simp [h1_mem]

/-- Algebraic decomposition: the full body splits as `loop_setup ++ main`. -/
theorem block_byte_prefix_body_eq :
    block_byte_prefix_body = loop_setup ++ block_byte_prefix_main := by
  rfl

end MemcpyProof.Hoare
