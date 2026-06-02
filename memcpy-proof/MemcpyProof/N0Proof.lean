/-
# Symbolic proof infrastructure for memcpy's n = 0 case

Goal: for any `regs`, `mem`, `haltAt` with `regs 12 = 0` (n=0) and
`regs 1 = haltAt`, memcpy halts having written nothing to memory.

Approach: instruction-by-instruction symbolic tracing.  For each PC `A`
on the n=0 path we expose a per-PC step lemma `step_at_A` reducing the
interpreter step to the explicit post-state.  These are chained via
`run_succ` and `rw`.

Branch resolution at each conditional uses bit-level facts (proved by
`bv_decide`) about the *symbolic* register values at that PC.  The
crucial bridge `run_4_regs13_nonzero` shows the `bne` at PC 0x200908
is taken under the n=0 hypothesis.
-/

import MemcpyProof.Harness
import MemcpyProof.RV32I
import Std.Tactic.BVDecide

namespace MemcpyProof.N0Proof

open MemcpyProof.Sem
open MemcpyProof.RV32I
open MemcpyProof.Harness
open MemcpyProof.Extract

set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-! ## Bit-level helper facts (discharged by `bv_decide`). -/

theorem or_one_ne_zero (x : UInt32) : (x ||| 1) ≠ 0 := by bv_decide
theorem and_zero (k : UInt32) : ((0 : UInt32) &&& k) = 0 := by bv_decide

/-! ## A custom tactic for single-step reduction.

Given a state with concrete `pc`, this unfolds the interpreter,
resolves the `if halted` check, and rewrites `code <pc>` to its
concrete word using one of the `code_at_X` lemmas. -/

/-- Rewrite `code <literal pc>` using one of the `code_at_X` lemmas. -/
syntax "rewrite_code" : tactic
macro_rules
  | `(tactic| rewrite_code) => `(tactic|
      first
        | rw [code_at_002008f8] | rw [code_at_002008fc]
        | rw [code_at_00200900] | rw [code_at_00200904]
        | rw [code_at_00200908] | rw [code_at_0020090c]
        | rw [code_at_00200950] | rw [code_at_00200954]
        | rw [code_at_00200a00] | rw [code_at_00200a04]
        | rw [code_at_00200a08] | rw [code_at_00200a0c]
        | rw [code_at_00200a10] | rw [code_at_00200a14]
        | rw [code_at_00200a4c] | rw [code_at_00200a50]
        | rw [code_at_00200a6c] | rw [code_at_00200a70]
        | rw [code_at_00200a18] | rw [code_at_00200a1c]
        | rw [code_at_00200a20] | rw [code_at_00200a24]
        | rw [code_at_00200a28] | rw [code_at_00200a2c]
        | rw [code_at_00200a30] | rw [code_at_00200a34]
        | rw [code_at_00200a38] | rw [code_at_00200a3c]
        | rw [code_at_00200a40] | rw [code_at_00200a44]
        | rw [code_at_00200a48]
        | rw [code_at_00200a54] | rw [code_at_00200a58]
        | rw [code_at_00200a5c] | rw [code_at_00200a60]
        | rw [code_at_00200a64] | rw [code_at_00200a68]
        | rw [code_at_00200a74] | rw [code_at_00200a78]
        | rw [code_at_00200a7c] | rw [code_at_00200a80]
        | rw [code_at_00200a84]
        | rw [code_at_00200b90] | rw [code_at_00200b94]
        | rw [code_at_00200b98] | rw [code_at_00200b9c]
        | rw [code_at_00200ba0] | rw [code_at_00200ba4]
        | rw [code_at_00200bd4] | rw [code_at_00200bd8]
        | rw [code_at_00200bdc] | rw [code_at_00200be0]
        | rw [code_at_00200be4] | rw [code_at_00200c0c]
        | rw [code_at_00200c10] | rw [code_at_00200c14])

/-- Reduce `step memcpyCode { … pc := <lit> … }` to its explicit
post-state.  Combines unfolding, the halted=false branch, code lookup,
exec unfolding, and the final reflexivity check. -/
syntax "step_reduce" : tactic
macro_rules
  | `(tactic| step_reduce) => `(tactic|
      (unfold step memcpyCode
       simp only [Bool.false_eq_true, ↓reduceIte]
       rewrite_code
       unfold exec
       simp only [getReg]
       rfl))

/-! ## Non-branch step lemmas. -/

theorem step_at_2008f8 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x002008f8, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then regs 11 &&& 3 else regs i,
        mem := mem, pc := 0x002008fc, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_2008fc (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x002008fc, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then (if regs 13 < 1 then 1 else 0) else regs i,
        mem := mem, pc := 0x00200900, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200900 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200900, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 14 then (if regs 12 < 1 then 1 else 0) else regs i,
        mem := mem, pc := 0x00200904, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200904 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200904, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then regs 13 ||| regs 14 else regs i,
        mem := mem, pc := 0x00200908, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a00 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a00, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then regs 10 + 0 else regs i,
        mem := mem, pc := 0x00200a04, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a04 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a04, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 14 then regs 11 + 0 else regs i,
        mem := mem, pc := 0x00200a08, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a08 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a08, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 13 &&& 3 else regs i,
        mem := mem, pc := 0x00200a0c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a10 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a10, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then 16 else regs i,
        mem := mem, pc := 0x00200a14, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a4c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 8 else regs i,
        mem := mem, pc := 0x00200a50, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a6c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a6c, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 4 else regs i,
        mem := mem, pc := 0x00200a70, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200bd4 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 2 else regs i,
        mem := mem, pc := 0x00200bd8, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200bdc (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200bdc, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 1 else regs i,
        mem := mem, pc := 0x00200be0, halted := false, haltAt := haltAt } := by step_reduce

/-! ### Step lemmas for the main copy loop body (n ≥ 16, both aligned). -/

theorem step_at_200a18 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a18, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then 15 else regs i,
        mem := mem, pc := 0x00200a1c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a1c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a1c, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 15 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 0) else regs i,
        mem := mem, pc := 0x00200a20, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a20 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a20, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 16 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 4) else regs i,
        mem := mem, pc := 0x00200a24, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a24 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a24, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 17 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 8) else regs i,
        mem := mem, pc := 0x00200a28, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a28 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a28, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 5 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 12) else regs i,
        mem := mem, pc := 0x00200a2c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a2c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a2c, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 0) (regs 15)).mem,
        pc := 0x00200a30, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a30 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a30, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 4) (regs 16)).mem,
        pc := 0x00200a34, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a34 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a34, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 8) (regs 17)).mem,
        pc := 0x00200a38, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a38 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a38, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 12) (regs 5)).mem,
        pc := 0x00200a3c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a3c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a3c, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 14 then regs 14 + 16 else regs i,
        mem := mem, pc := 0x00200a40, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a40 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a40, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 12 then regs 12 + (0xFFFFFFF0 : UInt32) else regs i,
        mem := mem, pc := 0x00200a44, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a44 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a44, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then regs 13 + 16 else regs i,
        mem := mem, pc := 0x00200a48, halted := false, haltAt := haltAt } := by step_reduce

/-! ### Case-B PC step lemmas (dst not aligned). -/

theorem step_at_200950 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200950, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 15 then 32 else regs i,
        mem := mem, pc := 0x00200954, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200b90 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200b90, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 16 else regs i,
        mem := mem, pc := 0x00200b94, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200b98 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200b98, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 8 else regs i,
        mem := mem, pc := 0x00200b9c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200ba0 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200ba0, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then regs 12 &&& 4 else regs i,
        mem := mem, pc := 0x00200ba4, halted := false, haltAt := haltAt } := by step_reduce

/-! ## Branch step lemmas (conditioned on the relevant register value). -/

/-- `bne a3, zero, +248` at PC 0x200908 — branch taken when `regs 13 ≠ 0`. -/
theorem step_at_200908_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ne : regs 13 ≠ 0) (h_no_halt : (0x00200a00 : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200908, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a00, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200908, halted := false, haltAt := haltAt }
    = if regs 13 != 0 then
        (if (0x00200a00 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200a00, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200a00, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x0020090c, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 13 != 0) = true := by rw [bne_iff_ne]; exact h_ne
  rw [h_cond]; simp only [↓reduceIte]
  have h_neq : ((0x00200a00 : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `bne a1, zero, -188` at PC 0x200a0c — NOT taken when `regs 11 = 0`. -/
theorem step_at_200a0c_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a0c, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a10, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a0c, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200950 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200950, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200950, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a10, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = false := by rw [bne_eq_false_iff_eq]; exact h_eq
  rw [h_cond]; rfl

/-- `bltu a2, a1, +56` at PC 0x200a14 — taken when `regs 12 < regs 11`. -/
theorem step_at_200a14_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_lt : regs 12 < regs 11) (h_no_halt : (0x00200a4c : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a14, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a14, halted := false, haltAt := haltAt }
    = if regs 12 < regs 11 then
        (if (0x00200a4c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200a4c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a18, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]; simp only [h_lt, ↓reduceIte]
  have h_neq : ((0x00200a4c : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `bltu a2, a1, +56` at PC 0x200a14 — NOT taken when `regs 12 ≥ regs 11`
(i.e. n ≥ 16 with regs 11 = 16). -/
theorem step_at_200a14_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ge : ¬ (regs 12 < regs 11)) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a14, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a18, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a14, halted := false, haltAt := haltAt }
    = if regs 12 < regs 11 then
        (if (0x00200a4c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200a4c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a18, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  simp [h_ge]

/-- `bltu a1, a2, -44` at PC 0x200a48 — TAKEN (loop back) when `regs 11 < regs 12`. -/
theorem step_at_200a48_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_lt : regs 11 < regs 12) (h_no_halt : (0x00200a1c : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a48, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a1c, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a48, halted := false, haltAt := haltAt }
    = if regs 11 < regs 12 then
        (if (0x00200a1c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200a1c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200a1c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]; simp only [h_lt, ↓reduceIte]
  have h_neq : ((0x00200a1c : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `bltu a1, a2, -44` at PC 0x200a48 — NOT taken (loop exit) when `regs 11 ≥ regs 12`. -/
theorem step_at_200a48_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ge : ¬ (regs 11 < regs 12)) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a48, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a48, halted := false, haltAt := haltAt }
    = if regs 11 < regs 12 then
        (if (0x00200a1c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200a1c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200a1c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a4c, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]; simp [h_ge]

/-- `beq a1, zero, +28` at PC 0x200a50 — taken when `regs 11 = 0`. -/
theorem step_at_200a50_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) (h_no_halt : (0x00200a6c : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a50, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200a6c, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a50, halted := false, haltAt := haltAt }
    = if regs 11 == 0 then
        (if (0x00200a6c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200a6c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200a6c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a54, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 == 0) = true := by rw [beq_iff_eq]; exact h_eq
  rw [h_cond]; simp only [↓reduceIte]
  have h_neq : ((0x00200a6c : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `beq a1, zero, +356` at PC 0x200a70 — taken when `regs 11 = 0`. -/
theorem step_at_200a70_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) (h_no_halt : (0x00200bd4 : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a70, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a70, halted := false, haltAt := haltAt }
    = if regs 11 == 0 then
        (if (0x00200bd4 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200bd4, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a74, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 == 0) = true := by rw [beq_iff_eq]; exact h_eq
  rw [h_cond]; simp only [↓reduceIte]
  have h_neq : ((0x00200bd4 : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `bne a1, zero, +16` at PC 0x200bd8 — NOT taken when `regs 11 = 0`. -/
theorem step_at_200bd8_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200bd8, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200bdc, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200bd8, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200be8 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200be8, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200be8, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200bdc, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = false := by rw [bne_eq_false_iff_eq]; exact h_eq
  rw [h_cond]; rfl

/-- `bne a1, zero, +44` at PC 0x200be0 — NOT taken when `regs 11 = 0`. -/
theorem step_at_200be0_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200be0, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200be4, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200be0, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200c0c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200c0c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200c0c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200be4, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = false := by rw [bne_eq_false_iff_eq]; exact h_eq
  rw [h_cond]; rfl

/-! ### Tail copy for n=1 case (both aligned). -/

theorem step_at_200c0c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200c0c, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then signExt (mem (regs 14 + 0)).toUInt32 7 else regs i,
        mem := mem, pc := 0x00200c10, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200c10 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200c10, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := fun a => if a == regs 13 + 0 then (regs 11).toUInt8 else mem a,
        pc := 0x00200c14, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200c14_ret (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ra : regs 1 = haltAt) (h_even : haltAt &&& 1 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200c14, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := haltAt, halted := true, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200c14, halted := false, haltAt := haltAt }
    = (if (regs 1 + 0 &&& ~~~1 : UInt32) == haltAt then
          { regs := regs, mem := mem, pc := regs 1 + 0 &&& ~~~1,
            halted := true, haltAt := haltAt }
       else
          { regs := regs, mem := mem, pc := regs 1 + 0 &&& ~~~1,
            halted := false, haltAt := haltAt }) := by
    step_reduce
  rw [h, h_ra]
  have h_mask : haltAt + 0 &&& ~~~1 = haltAt := by
    have h1 : haltAt + 0 = haltAt := by bv_decide
    rw [h1]; bv_decide
  rw [h_mask]; simp

/-- `bne a1, zero, +44` at PC 0x200be0 — TAKEN when `regs 11 ≠ 0`.
    For n=1 (so `n & 1 = 1`), this branch fires to do the final byte copy. -/
theorem step_at_200be0_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ne : regs 11 ≠ 0) (h_no_halt : (0x00200c0c : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200be0, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200c0c, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200be0, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200c0c : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200c0c, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200c0c, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200be4, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = true := by rw [bne_iff_ne]; exact h_ne
  rw [h_cond]; simp only [↓reduceIte]
  have h_neq : ((0x00200c0c : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-! ### Step lemmas for the 8-byte and 4-byte tail copies. -/

theorem step_at_200a54 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a54, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 0) else regs i,
        mem := mem, pc := 0x00200a58, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a58 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a58, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 15 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 4) else regs i,
        mem := mem, pc := 0x00200a5c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a5c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a5c, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 0) (regs 11)).mem,
        pc := 0x00200a60, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a60 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a60, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 4) (regs 15)).mem,
        pc := 0x00200a64, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a64 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a64, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then regs 13 + 8 else regs i,
        mem := mem, pc := 0x00200a68, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a68 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a68, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 14 then regs 14 + 8 else regs i,
        mem := mem, pc := 0x00200a6c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a74 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a74, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 11 then loadWord ⟨regs, mem, 0, false, haltAt⟩ (regs 14 + 0) else regs i,
        mem := mem, pc := 0x00200a78, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a78 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a78, halted := false, haltAt := haltAt } =
      { regs := regs,
        mem := (storeWord ⟨regs, mem, 0, false, haltAt⟩ (regs 13 + 0) (regs 11)).mem,
        pc := 0x00200a7c, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a7c (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a7c, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 13 then regs 13 + 4 else regs i,
        mem := mem, pc := 0x00200a80, halted := false, haltAt := haltAt } := by step_reduce

theorem step_at_200a80 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a80, halted := false, haltAt := haltAt } =
      { regs := fun i => if i == 14 then regs 14 + 4 else regs i,
        mem := mem, pc := 0x00200a84, halted := false, haltAt := haltAt } := by step_reduce

/-- `jal zero, +336` at PC 0x200a84 — unconditional jump to 0x200bd4. -/
theorem step_at_200a84_jal (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_no_halt : (0x00200bd4 : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a84, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a84, halted := false, haltAt := haltAt }
    = (if (0x00200bd4 : UInt32) == haltAt then
          { regs := regs, mem := mem, pc := 0x00200bd4, halted := true, haltAt := haltAt }
       else
          { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt }) := by
    step_reduce
  rw [h]
  have h_neq : ((0x00200bd4 : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-! ### Case-B branch step lemmas. -/

/-- `bne a1, zero, -188` at PC 0x200a0c — branch TAKEN when `regs 11 ≠ 0`. -/
theorem step_at_200a0c_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ne : regs 11 ≠ 0) (h_no_halt : (0x00200950 : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200a0c, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200950, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200a0c, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200950 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200950, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200950, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200a10, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = true := by rw [bne_iff_ne]; exact h_ne
  rw [h_cond]; simp only [↓reduceIte]
  have h_neq : ((0x00200950 : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `bltu a2, a5, +572` at PC 0x200954 — branch taken when `regs 12 < regs 15`. -/
theorem step_at_200954_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_lt : regs 12 < regs 15) (h_no_halt : (0x00200b90 : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200954, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200b90, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200954, halted := false, haltAt := haltAt }
    = if regs 12 < regs 15 then
        (if (0x00200b90 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200b90, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200b90, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200958, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]; simp only [h_lt, ↓reduceIte]
  have h_neq : ((0x00200b90 : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `bne a1, zero, +132` at PC 0x200b94 — NOT taken when `regs 11 = 0`. -/
theorem step_at_200b94_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200b94, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200b98, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200b94, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200c18 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200c18, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200c18, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200b98, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = false := by rw [bne_eq_false_iff_eq]; exact h_eq
  rw [h_cond]; rfl

/-- `bne a1, zero, +272` at PC 0x200b9c — NOT taken when `regs 11 = 0`. -/
theorem step_at_200b9c_not_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200b9c, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200ba0, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200b9c, halted := false, haltAt := haltAt }
    = if regs 11 != 0 then
        (if (0x00200cac : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200cac, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200cac, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200ba0, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 != 0) = false := by rw [bne_eq_false_iff_eq]; exact h_eq
  rw [h_cond]; rfl

/-- `beq a1, zero, +48` at PC 0x200ba4 — taken when `regs 11 = 0`. -/
theorem step_at_200ba4_taken (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_eq : regs 11 = 0) (h_no_halt : (0x00200bd4 : UInt32) ≠ haltAt) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200ba4, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200ba4, halted := false, haltAt := haltAt }
    = if regs 11 == 0 then
        (if (0x00200bd4 : UInt32) == haltAt then
            { regs := regs, mem := mem, pc := 0x00200bd4, halted := true, haltAt := haltAt }
         else
            { regs := regs, mem := mem, pc := 0x00200bd4, halted := false, haltAt := haltAt })
      else
        { regs := regs, mem := mem, pc := 0x00200ba8, halted := false, haltAt := haltAt } := by
    step_reduce
  rw [h]
  have h_cond : (regs 11 == 0) = true := by rw [beq_iff_eq]; exact h_eq
  rw [h_cond]; simp only [↓reduceIte]
  have h_neq : ((0x00200bd4 : UInt32) == haltAt) = false := by
    rw [beq_eq_false_iff_ne]; exact h_no_halt
  rw [h_neq]; rfl

/-- `jalr zero, 0(ra)` at PC 0x200be4 — RET, sets halted when `regs 1 = haltAt`
and `haltAt` is even. -/
theorem step_at_200be4_ret (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_ra : regs 1 = haltAt) (h_even : haltAt &&& 1 = 0) :
    step memcpyCode { regs := regs, mem := mem, pc := 0x00200be4, halted := false, haltAt := haltAt } =
      { regs := regs, mem := mem, pc := haltAt, halted := true, haltAt := haltAt } := by
  have h : step memcpyCode
      { regs := regs, mem := mem, pc := 0x00200be4, halted := false, haltAt := haltAt }
    = (if (regs 1 + 0 &&& ~~~1 : UInt32) == haltAt then
          { regs := regs, mem := mem, pc := regs 1 + 0 &&& ~~~1,
            halted := true, haltAt := haltAt }
       else
          { regs := regs, mem := mem, pc := regs 1 + 0 &&& ~~~1,
            halted := false, haltAt := haltAt }) := by
    step_reduce
  rw [h, h_ra]
  have h_mask : haltAt + 0 &&& ~~~1 = haltAt := by
    have h1 : haltAt + 0 = haltAt := by bv_decide
    rw [h1]; bv_decide
  rw [h_mask]
  simp

/-! ## Chaining helpers — see `Sem.lean` for `run_succ`, `run_add`. -/

/-! ## Prefix chain: after 4 steps. -/

theorem run_4_pc_and_mem (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    let s := run memcpyCode 4
              { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
                haltAt := haltAt }
    s.pc = 0x00200908 ∧ s.mem = mem ∧ s.halted = false := by
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_2008f8]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_2008fc]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200900]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200904]
  refine ⟨rfl, rfl, rfl⟩

theorem run_4_regs14 (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    (run memcpyCode 4
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).regs 14
    = (if regs 12 < 1 then 1 else 0) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_2008f8]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_2008fc]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200900]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200904]
  rfl

/-- The key bridge: under `regs 12 = 0`, after 4 steps `regs 13 ≠ 0`. -/
theorem run_4_regs13_nonzero (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h : regs 12 = 0) :
    (run memcpyCode 4
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).regs 13 ≠ 0 := by
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_2008f8]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_2008fc]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200900]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200904]
  show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
  rw [h]
  show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| 1) ≠ 0
  exact or_one_ne_zero _

/-! ## Final theorem (TODO). -/

/-! ## Case A: n=0 with dst aligned (`dst & 3 = 0`).

Trace: 0x2008f8 → 0x2008fc → 0x200900 → 0x200904 → 0x200908 (bne taken to
0x200a00) → 0x200a00 → 0x200a04 → 0x200a08 → 0x200a0c (bne not taken
because dst aligned) → 0x200a10 → 0x200a14 (bltu taken to 0x200a4c) →
0x200a4c → 0x200a50 (beq taken to 0x200a6c) → 0x200a6c → 0x200a70
(beq taken to 0x200bd4) → 0x200bd4 → 0x200bd8 (bne not taken) →
0x200bdc → 0x200be0 (bne not taken) → 0x200be4 (ret).
19 steps, no memory writes.
-/

/-- After 5 steps we have taken the `bne` branch and PC = 0x200a00. -/
theorem run_5_case_A
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 0)
    (h_no_halt_a00 : (0x00200a00 : UInt32) ≠ haltAt) :
    (run memcpyCode 5
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).pc = 0x00200a00 := by
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200908_taken _ _ _ ?_ h_no_halt_a00]
  · rfl
  · show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_a2]; exact or_one_ne_zero _

/-- After 5 steps, the memory is unchanged. -/
theorem run_5_case_A_mem
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 0)
    (h_no_halt_a00 : (0x00200a00 : UInt32) ≠ haltAt) :
    (run memcpyCode 5
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).mem = mem := by
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200908_taken _ _ _ ?_ h_no_halt_a00]
  · rfl
  · show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_a2]; exact or_one_ne_zero _

/-- After 5 steps, the routine has not halted yet. -/
theorem run_5_case_A_halted
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 0)
    (h_no_halt_a00 : (0x00200a00 : UInt32) ≠ haltAt) :
    (run memcpyCode 5
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).halted = false := by
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200908_taken _ _ _ ?_ h_no_halt_a00]
  · rfl
  · show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_a2]; exact or_one_ne_zero _

/-- Full chained proof for case A: dst & 3 = 0.  After 20 steps the
routine has executed `ret`, *and* `mem` is unchanged (no store on the path). -/
theorem memcpy_n0_case_A_full
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 0)
    (h_dst : regs 10 &&& 3 = 0)
    (h_ra : regs 1 = haltAt)
    (h_even : haltAt &&& 1 = 0)
    (h_no_a00 : (0x00200a00 : UInt32) ≠ haltAt)
    (h_no_a4c : (0x00200a4c : UInt32) ≠ haltAt)
    (h_no_a6c : (0x00200a6c : UInt32) ≠ haltAt)
    (h_no_bd4 : (0x00200bd4 : UInt32) ≠ haltAt) :
    (run memcpyCode 20
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).halted = true ∧
    (run memcpyCode 20
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).mem = mem := by
  refine ⟨?halted, ?mem⟩
  all_goals
    (
  rw [show (20 : Nat) = 19 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (19 : Nat) = 18 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (18 : Nat) = 17 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (17 : Nat) = 16 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  -- Step 5: bne taken at 0x200908
  rw [show (16 : Nat) = 15 + 1 from rfl, run_succ _ _ rfl,
      step_at_200908_taken _ _ _ ?h5 h_no_a00]
  case h5 =>
    show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_a2]; exact or_one_ne_zero _
  rw [show (15 : Nat) = 14 + 1 from rfl, run_succ _ _ rfl, step_at_200a00]
  rw [show (14 : Nat) = 13 + 1 from rfl, run_succ _ _ rfl, step_at_200a04]
  rw [show (13 : Nat) = 12 + 1 from rfl, run_succ _ _ rfl, step_at_200a08]
  -- Step 9: bne not taken at 0x200a0c (regs 11 = dst & 3 = 0)
  rw [show (12 : Nat) = 11 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a0c_not_taken _ _ _ ?h9]
  case h9 =>
    show regs 10 + 0 &&& 3 = 0
    have : regs 10 + 0 = regs 10 := by bv_decide
    rw [this]; exact h_dst
  rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_200a10]
  -- Step 11: bltu taken at 0x200a14 (0 < 16)
  rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a14_taken _ _ _ ?h11 h_no_a4c]
  case h11 =>
    show regs 12 < 16
    rw [h_a2]; decide
  rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200a4c]
  -- Step 13: beq taken at 0x200a50 (regs 11 = n & 8 = 0)
  rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a50_taken _ _ _ ?h13 h_no_a6c]
  case h13 =>
    show regs 12 &&& 8 = 0
    rw [h_a2]; decide
  rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl, step_at_200a6c]
  -- Step 15: beq taken at 0x200a70 (regs 11 = n & 4 = 0)
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a70_taken _ _ _ ?h15 h_no_bd4]
  case h15 =>
    show regs 12 &&& 4 = 0
    rw [h_a2]; decide
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200bd4]
  -- Step 17: bne not taken at 0x200bd8 (regs 11 = n & 2 = 0)
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl,
      step_at_200bd8_not_taken _ _ _ ?h17]
  case h17 =>
    show regs 12 &&& 2 = 0
    rw [h_a2]; decide
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200bdc]
  -- Step 19: bne not taken at 0x200be0 (regs 11 = n & 1 = 0)
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl,
      step_at_200be0_not_taken _ _ _ ?h19]
  case h19 =>
    show regs 12 &&& 1 = 0
    rw [h_a2]; decide
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  -- After 19 setRegs, register 1 (ra) was never written, so it still equals
  -- the original `regs 1 = haltAt`.
  rw [step_at_200be4_ret _ _ _ (show _ = haltAt by simp; exact h_ra) h_even]
  rfl)

/-- Full chained proof for case B: dst & 3 ≠ 0.  After 22 steps the
routine has executed `ret`, and mem is unchanged. -/
theorem memcpy_n0_case_B_full
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 0)
    (h_dst : regs 10 &&& 3 ≠ 0)
    (h_ra : regs 1 = haltAt)
    (h_even : haltAt &&& 1 = 0)
    (h_no_a00 : (0x00200a00 : UInt32) ≠ haltAt)
    (h_no_950 : (0x00200950 : UInt32) ≠ haltAt)
    (h_no_b90 : (0x00200b90 : UInt32) ≠ haltAt)
    (h_no_bd4 : (0x00200bd4 : UInt32) ≠ haltAt) :
    (run memcpyCode 22
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).halted = true ∧
    (run memcpyCode 22
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).mem = mem := by
  refine ⟨?halted, ?mem⟩
  all_goals
    (rw [show (22 : Nat) = 21 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
     rw [show (21 : Nat) = 20 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
     rw [show (20 : Nat) = 19 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
     rw [show (19 : Nat) = 18 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
     rw [show (18 : Nat) = 17 + 1 from rfl, run_succ _ _ rfl,
         step_at_200908_taken _ _ _ ?h5 h_no_a00]
     case h5 =>
       show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
       rw [h_a2]; exact or_one_ne_zero _
     rw [show (17 : Nat) = 16 + 1 from rfl, run_succ _ _ rfl, step_at_200a00]
     rw [show (16 : Nat) = 15 + 1 from rfl, run_succ _ _ rfl, step_at_200a04]
     rw [show (15 : Nat) = 14 + 1 from rfl, run_succ _ _ rfl, step_at_200a08]
     -- Step 9: bne TAKEN at 0x200a0c (dst not aligned).
     rw [show (14 : Nat) = 13 + 1 from rfl, run_succ _ _ rfl,
         step_at_200a0c_taken _ _ _ ?h9 h_no_950]
     case h9 =>
       show regs 10 + 0 &&& 3 ≠ 0
       have : regs 10 + 0 = regs 10 := by bv_decide
       rw [this]; exact h_dst
     rw [show (13 : Nat) = 12 + 1 from rfl, run_succ _ _ rfl, step_at_200950]
     -- Step 11: bltu taken at 0x200954 (0 < 32).
     rw [show (12 : Nat) = 11 + 1 from rfl, run_succ _ _ rfl,
         step_at_200954_taken _ _ _ ?h11 h_no_b90]
     case h11 =>
       show regs 12 < 32
       rw [h_a2]; decide
     rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_200b90]
     -- Step 13: bne not taken at 0x200b94.
     rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl,
         step_at_200b94_not_taken _ _ _ ?h13]
     case h13 =>
       show regs 12 &&& 16 = 0
       rw [h_a2]; decide
     rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200b98]
     -- Step 15: bne not taken at 0x200b9c.
     rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl,
         step_at_200b9c_not_taken _ _ _ ?h15]
     case h15 =>
       show regs 12 &&& 8 = 0
       rw [h_a2]; decide
     rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl, step_at_200ba0]
     -- Step 17: beq taken at 0x200ba4.
     rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl,
         step_at_200ba4_taken _ _ _ ?h17 h_no_bd4]
     case h17 =>
       show regs 12 &&& 4 = 0
       rw [h_a2]; decide
     rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200bd4]
     -- Step 19: bne not taken at 0x200bd8.
     rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl,
         step_at_200bd8_not_taken _ _ _ ?h19]
     case h19 =>
       show regs 12 &&& 2 = 0
       rw [h_a2]; decide
     rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200bdc]
     -- Step 21: bne not taken at 0x200be0.
     rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl,
         step_at_200be0_not_taken _ _ _ ?h21]
     case h21 =>
       show regs 12 &&& 1 = 0
       rw [h_a2]; decide
     rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
     rw [step_at_200be4_ret _ _ _ (show _ = haltAt by simp; exact h_ra) h_even]
     rfl)

/-! ## n=32 case (both src and dst aligned) — chunked symbolic proof.

The 45-step chain doesn't fit in a single tactic block (state size grows
too fast).  We break it into chunks, each proving an intermediate
state-projection equality (`.pc = X ∧ .halted = false`) and threading
the relevant *register values* via additional `have`s.  Memory contents
do change (the routine performs 8 word stores), but for termination we
only need to track PC and a few key registers. -/

/-! ## Block-level semantics: the 16-byte main loop body.

`block_F` characterizes the 12 instructions from PC 0x200a18 through
PC 0x200a48: load 4 words from `regs 14`..`regs 14 + 15`, store them
to `regs 13`..`regs 13 + 15`, advance the three working pointers
(`regs 12 -= 16`, `regs 13 += 16`, `regs 14 += 16`).

This is the heart of memcpy's aligned fast-path.  Once we have this
block lemma, an inductive proof on `regs 12 / 16` discharges the
arbitrary-aligned-multiple-of-16 cases. -/

/-- The 4 words loaded from `regs 14..regs 14 + 15` are written verbatim
to `regs 13..regs 13 + 15`. -/
theorem block_F (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    let src := regs 14
    let dst := regs 13
    let w0 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 0)
    let w1 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 4)
    let w2 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 8)
    let w3 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 12)
    let s0 : State := { regs := regs, mem := mem, pc := 0x00200a18, halted := false, haltAt := haltAt }
    let m1 := (storeWord s0 (dst + 0) w0).mem
    let m2 := (storeWord { s0 with mem := m1 } (dst + 4) w1).mem
    let m3 := (storeWord { s0 with mem := m2 } (dst + 8) w2).mem
    let m4 := (storeWord { s0 with mem := m3 } (dst + 12) w3).mem
    run memcpyCode 12 s0 = {
      regs := fun i =>
        if i == 13 then dst + 16
        else if i == 12 then regs 12 + 0xFFFFFFF0
        else if i == 14 then src + 16
        else if i == 5 then w3
        else if i == 17 then w2
        else if i == 16 then w1
        else if i == 15 then w0
        else if i == 11 then 15
        else regs i,
      mem := m4,
      pc := 0x00200a48, halted := false, haltAt := haltAt
    } := by
  simp only
  rw [show (12 : Nat) = 11 + 1 from rfl, run_succ _ _ rfl, step_at_200a18]
  rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_200a1c]
  rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl, step_at_200a20]
  rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200a24]
  rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl, step_at_200a28]
  rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl, step_at_200a2c]
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl, step_at_200a30]
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200a34]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_200a38]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200a3c]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200a40]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl, step_at_200a44]
  rfl

/-- The 16-byte main loop **iteration** (without the initial `addi a1, zero, 15`).
Starting at PC 0x200a1c.  This is what the `bltu` loops back to. -/
theorem block_F_iter (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    let src := regs 14
    let dst := regs 13
    let w0 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 0)
    let w1 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 4)
    let w2 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 8)
    let w3 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 12)
    let s0 : State := { regs := regs, mem := mem, pc := 0x00200a1c, halted := false, haltAt := haltAt }
    let m1 := (storeWord s0 (dst + 0) w0).mem
    let m2 := (storeWord { s0 with mem := m1 } (dst + 4) w1).mem
    let m3 := (storeWord { s0 with mem := m2 } (dst + 8) w2).mem
    let m4 := (storeWord { s0 with mem := m3 } (dst + 12) w3).mem
    run memcpyCode 11 s0 = {
      regs := fun i =>
        if i == 13 then dst + 16
        else if i == 12 then regs 12 + 0xFFFFFFF0
        else if i == 14 then src + 16
        else if i == 5 then w3
        else if i == 17 then w2
        else if i == 16 then w1
        else if i == 15 then w0
        else regs i,
      mem := m4,
      pc := 0x00200a48, halted := false, haltAt := haltAt
    } := by
  simp only
  rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_200a1c]
  rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl, step_at_200a20]
  rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200a24]
  rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl, step_at_200a28]
  rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl, step_at_200a2c]
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl, step_at_200a30]
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200a34]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_200a38]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200a3c]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200a40]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl, step_at_200a44]
  rfl

/-- **8-byte copy block** at PC 0x200a54.  Reads 8 bytes from `regs 14`,
writes them to `regs 13`, advances both pointers by 8. -/
theorem block_8byte (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    let src := regs 14
    let dst := regs 13
    let w0 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 0)
    let w1 := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 4)
    let s0 : State := { regs := regs, mem := mem, pc := 0x00200a54, halted := false, haltAt := haltAt }
    let m1 := (storeWord s0 (dst + 0) w0).mem
    let m2 := (storeWord { s0 with mem := m1 } (dst + 4) w1).mem
    run memcpyCode 6 s0 = {
      regs := fun i =>
        if i == 14 then src + 8
        else if i == 13 then dst + 8
        else if i == 15 then w1
        else if i == 11 then w0
        else regs i,
      mem := m2,
      pc := 0x00200a6c, halted := false, haltAt := haltAt
    } := by
  simp only
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl, step_at_200a54]
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200a58]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_200a5c]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200a60]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200a64]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl, step_at_200a68]
  rfl

/-- **4-byte copy block** at PC 0x200a74.  Reads 4 bytes from `regs 14`,
writes them to `regs 13`, advances both pointers by 4. -/
theorem block_4byte (regs : Regs) (mem : Mem) (haltAt : UInt32) :
    let src := regs 14
    let dst := regs 13
    let w := loadWord ⟨regs, mem, 0, false, haltAt⟩ (src + 0)
    let s0 : State := { regs := regs, mem := mem, pc := 0x00200a74, halted := false, haltAt := haltAt }
    let m1 := (storeWord s0 (dst + 0) w).mem
    run memcpyCode 4 s0 = {
      regs := fun i =>
        if i == 14 then src + 4
        else if i == 13 then dst + 4
        else if i == 11 then w
        else regs i,
      mem := m1,
      pc := 0x00200a84, halted := false, haltAt := haltAt
    } := by
  simp only
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_200a74]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200a78]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200a7c]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl, step_at_200a80]
  rfl

section
set_option maxHeartbeats 16000000

/-- After 23 steps from the start of memcpy (with n=32, both aligned), PC reaches
0x200a48 — i.e., we've finished the prefix, the initial `addi a1, zero, 15`,
and one full pass of the 16-byte main loop body (block_F). -/
theorem n32_pc_after_first_loop_iter
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_n : regs 12 = 32)
    (h_src : regs 11 &&& 3 = 0)
    (h_dst : regs 10 &&& 3 = 0)
    (h_no_a00 : (0x00200a00 : UInt32) ≠ haltAt) :
    (run memcpyCode 23
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).pc = 0x00200a48 := by
  rw [show (23 : Nat) = 22 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (22 : Nat) = 21 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (21 : Nat) = 20 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (20 : Nat) = 19 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  rw [show (19 : Nat) = 18 + 1 from rfl, run_succ _ _ rfl,
      step_at_200908_taken _ _ _ ?h5 h_no_a00]
  case h5 =>
    show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_src]; bv_decide
  rw [show (18 : Nat) = 17 + 1 from rfl, run_succ _ _ rfl, step_at_200a00]
  rw [show (17 : Nat) = 16 + 1 from rfl, run_succ _ _ rfl, step_at_200a04]
  rw [show (16 : Nat) = 15 + 1 from rfl, run_succ _ _ rfl, step_at_200a08]
  rw [show (15 : Nat) = 14 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a0c_not_taken _ _ _ ?h9]
  case h9 =>
    show regs 10 + 0 &&& 3 = 0
    have : regs 10 + 0 = regs 10 := by bv_decide
    rw [this]; exact h_dst
  rw [show (14 : Nat) = 13 + 1 from rfl, run_succ _ _ rfl, step_at_200a10]
  rw [show (13 : Nat) = 12 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a14_not_taken _ _ _ ?h11]
  case h11 =>
    show ¬ (regs 12 < 16)
    rw [h_n]; decide
  rw [show (12 : Nat) = 11 + 1 from rfl, run_succ _ _ rfl, step_at_200a18]
  rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_200a1c]
  rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl, step_at_200a20]
  rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200a24]
  rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl, step_at_200a28]
  rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl, step_at_200a2c]
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl, step_at_200a30]
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200a34]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_200a38]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200a3c]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200a40]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl, step_at_200a44]
  rfl

end

/-- Chunk 1: prefix + dst-aligned check + n≥16 check, ending at PC 0x200a18
with `regs 11 = 16` and `regs 12 = 32`.  11 steps. -/
theorem n32_chunk1
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_n : regs 12 = 32)
    (h_src : regs 11 &&& 3 = 0)
    (h_dst : regs 10 &&& 3 = 0)
    (h_no_a00 : (0x00200a00 : UInt32) ≠ haltAt) :
    (run memcpyCode 11
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).pc = 0x00200a18 := by
  rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl,
      step_at_200908_taken _ _ _ ?h5 h_no_a00]
  case h5 =>
    show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_src]; bv_decide
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl, step_at_200a00]
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200a04]
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl, step_at_200a08]
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a0c_not_taken _ _ _ ?h9]
  case h9 =>
    show regs 10 + 0 &&& 3 = 0
    have : regs 10 + 0 = regs 10 := by bv_decide
    rw [this]; exact h_dst
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200a10]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a14_not_taken _ _ _ ?h11]
  case h11 =>
    show ¬ (regs 12 < 16)
    rw [h_n]; decide
  rfl

/-! ## n=1 case (both src and dst aligned).

We push the technique to a non-zero n to demonstrate the approach
generalises.  For n=1 with src and dst both aligned, the routine takes
the same prefix as n=0 case A until step 19, where the `bne` at PC
0x200be0 *is* taken (because `n & 1 = 1`).  This jumps to a 3-instruction
byte-copy tail (`lb`, `sb`, `ret`).  Total: 22 steps. -/

theorem memcpy_n1_both_aligned_halts
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 1)
    (h_src : regs 11 &&& 3 = 0)
    (h_dst : regs 10 &&& 3 = 0)
    (h_ra : regs 1 = haltAt)
    (h_even : haltAt &&& 1 = 0)
    (h_no_a00 : (0x00200a00 : UInt32) ≠ haltAt)
    (h_no_a4c : (0x00200a4c : UInt32) ≠ haltAt)
    (h_no_a6c : (0x00200a6c : UInt32) ≠ haltAt)
    (h_no_bd4 : (0x00200bd4 : UInt32) ≠ haltAt)
    (h_no_c0c : (0x00200c0c : UInt32) ≠ haltAt) :
    (run memcpyCode 22
        { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
          haltAt := haltAt }).halted = true := by
  rw [show (22 : Nat) = 21 + 1 from rfl, run_succ _ _ rfl, step_at_2008f8]
  rw [show (21 : Nat) = 20 + 1 from rfl, run_succ _ _ rfl, step_at_2008fc]
  rw [show (20 : Nat) = 19 + 1 from rfl, run_succ _ _ rfl, step_at_200900]
  rw [show (19 : Nat) = 18 + 1 from rfl, run_succ _ _ rfl, step_at_200904]
  rw [show (18 : Nat) = 17 + 1 from rfl, run_succ _ _ rfl,
      step_at_200908_taken _ _ _ ?h5 h_no_a00]
  case h5 =>
    show ((if regs 11 &&& 3 < 1 then 1 else 0) ||| (if regs 12 < 1 then 1 else 0)) ≠ 0
    rw [h_src]
    show ((1 : UInt32) ||| _) ≠ 0
    bv_decide
  rw [show (17 : Nat) = 16 + 1 from rfl, run_succ _ _ rfl, step_at_200a00]
  rw [show (16 : Nat) = 15 + 1 from rfl, run_succ _ _ rfl, step_at_200a04]
  rw [show (15 : Nat) = 14 + 1 from rfl, run_succ _ _ rfl, step_at_200a08]
  rw [show (14 : Nat) = 13 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a0c_not_taken _ _ _ ?h9]
  case h9 =>
    show regs 10 + 0 &&& 3 = 0
    have : regs 10 + 0 = regs 10 := by bv_decide
    rw [this]; exact h_dst
  rw [show (13 : Nat) = 12 + 1 from rfl, run_succ _ _ rfl, step_at_200a10]
  rw [show (12 : Nat) = 11 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a14_taken _ _ _ ?h11 h_no_a4c]
  case h11 =>
    show regs 12 < 16
    rw [h_a2]; decide
  rw [show (11 : Nat) = 10 + 1 from rfl, run_succ _ _ rfl, step_at_200a4c]
  rw [show (10 : Nat) = 9 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a50_taken _ _ _ ?h13 h_no_a6c]
  case h13 =>
    show regs 12 &&& 8 = 0
    rw [h_a2]; decide
  rw [show (9 : Nat) = 8 + 1 from rfl, run_succ _ _ rfl, step_at_200a6c]
  rw [show (8 : Nat) = 7 + 1 from rfl, run_succ _ _ rfl,
      step_at_200a70_taken _ _ _ ?h15 h_no_bd4]
  case h15 =>
    show regs 12 &&& 4 = 0
    rw [h_a2]; decide
  rw [show (7 : Nat) = 6 + 1 from rfl, run_succ _ _ rfl, step_at_200bd4]
  rw [show (6 : Nat) = 5 + 1 from rfl, run_succ _ _ rfl,
      step_at_200bd8_not_taken _ _ _ ?h17]
  case h17 =>
    show regs 12 &&& 2 = 0
    rw [h_a2]; decide
  rw [show (5 : Nat) = 4 + 1 from rfl, run_succ _ _ rfl, step_at_200bdc]
  -- Step 19: bne at 0x200be0 is TAKEN (n & 1 = 1).
  rw [show (4 : Nat) = 3 + 1 from rfl, run_succ _ _ rfl,
      step_at_200be0_taken _ _ _ ?h19 h_no_c0c]
  case h19 =>
    show regs 12 &&& 1 ≠ 0
    rw [h_a2]; decide
  rw [show (3 : Nat) = 2 + 1 from rfl, run_succ _ _ rfl, step_at_200c0c]
  rw [show (2 : Nat) = 1 + 1 from rfl, run_succ _ _ rfl, step_at_200c10]
  rw [show (1 : Nat) = 0 + 1 from rfl, run_succ _ _ rfl]
  rw [step_at_200c14_ret _ _ _ (show _ = haltAt by simp; exact h_ra) h_even]
  rfl

/-- The full n=0 correctness theorem, parametric in dst alignment.
For any registers with `regs 12 = 0` (n=0), the routine halts with
memory unchanged.  Fuel of 22 steps suffices for both alignment paths. -/
theorem memcpy_n0_correct
    (regs : Regs) (mem : Mem) (haltAt : UInt32)
    (h_a2 : regs 12 = 0)
    (h_ra : regs 1 = haltAt)
    (h_even : haltAt &&& 1 = 0)
    (h_no_a00 : (0x00200a00 : UInt32) ≠ haltAt)
    (h_no_a4c : (0x00200a4c : UInt32) ≠ haltAt)
    (h_no_a6c : (0x00200a6c : UInt32) ≠ haltAt)
    (h_no_bd4 : (0x00200bd4 : UInt32) ≠ haltAt)
    (h_no_950 : (0x00200950 : UInt32) ≠ haltAt)
    (h_no_b90 : (0x00200b90 : UInt32) ≠ haltAt) :
    ∃ k : Nat,
      (run memcpyCode k
          { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
            haltAt := haltAt }).halted = true ∧
      (run memcpyCode k
          { regs := regs, mem := mem, pc := 0x002008f8, halted := false,
            haltAt := haltAt }).mem = mem := by
  by_cases h_dst : regs 10 &&& 3 = 0
  · -- dst aligned: case A, fuel 20.
    exact ⟨20, memcpy_n0_case_A_full regs mem haltAt h_a2 h_dst h_ra h_even
            h_no_a00 h_no_a4c h_no_a6c h_no_bd4⟩
  · -- dst not aligned: case B, fuel 22.
    exact ⟨22, memcpy_n0_case_B_full regs mem haltAt h_a2 h_dst h_ra h_even
            h_no_a00 h_no_950 h_no_b90 h_no_bd4⟩

end MemcpyProof.N0Proof
