/-
CFG-level semantics of the byte-prefix loop (B2).

Full CFG-level correctness of the byte-prefix loop, dynamically
following PCs and honoring the back-edge of the bne.  Composed via
`CFG.do_while` from four obligations: `loop_inv_init`, `loop_inv_step`,
`loop_inv_exit`, and `K_pos_of_pre`.

Address summary (from the disassembly):
  0x20090c  loop_setup           (2 instrs)
  0x200914  loop_copy_byte       (4 instrs)  ← loop-back target of bne
  0x200924  loop_predicate       (5 instrs)
  0x200938  loop_branch          (3 addi + bne, 4 instrs total)
  0x200944  bne a7,zero,-48
  0x200948  fall-through to B3 (alignment dispatch)
-/

import MemcpyProof.Hoare.CFG
import MemcpyProof.Hoare.Blocks.BytePrefix
import MemcpyProof.Extract

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-- Shortcut for the memcpy program's `code` lookup. -/
abbrev mc : UInt32 → UInt32 := MemcpyProof.Extract.code

/-! ## 0. Loop precondition and iteration count.

The loop is entered only when `src` is misaligned AND `n > 0` (B1's bne
ensures this).  Under that precondition the loop runs
`K = min(4 - (a1 & 3), a2)` iterations, with `K ∈ {1, 2, 3}`. -/

/-- Preconditions for the byte-prefix loop:
    reachability (`src` misaligned ∧ `n ≠ 0`), non-aliasing of the
    src/dst windows, and no 32-bit pointer wraparound. -/
def Pre_loop_byte_prefix (s : State) : Prop :=
  let a0 := getReg s 10
  let a1 := getReg s 11
  let a2 := getReg s 12
  (a1 &&& 3) ≠ 0 ∧
  a2 ≠ 0 ∧
  (∀ i j : UInt32, i < a2 → j < a2 → a0 + i ≠ a1 + j) ∧
  a0.toNat + a2.toNat ≤ 2 ^ 32 ∧
  a1.toNat + a2.toNat ≤ 2 ^ 32

/-- `K(s)` — the loop's iteration count, derived from `s` alone. -/
def loop_byte_prefix_count (s : State) : UInt32 :=
  let a1 := getReg s 11
  let a2 := getReg s 12
  let K_align : UInt32 := 4 - (a1 &&& 3)
  if K_align ≤ a2 then K_align else a2

/-! ## 1. Per-block code-match lemmas.

For each of our four sub-blocks, prove that `mc` at the block's entry
PC decodes to exactly the block's instruction list (via
`CodeMatchesBlock`).  These should be discharged by `decide`/`rfl`
using the per-PC `code_at_*` equations in `Extract.lean`. -/

theorem mc_matches_loop_setup (s : State) (h : s.pc = 0x20090c) :
    CodeMatchesBlock mc s loop_setup := by mc_matches

theorem mc_matches_loop_copy_byte (s : State) (h : s.pc = 0x200914) :
    CodeMatchesBlock mc s loop_copy_byte := by mc_matches

theorem mc_matches_loop_predicate (s : State) (h : s.pc = 0x200924) :
    CodeMatchesBlock mc s loop_predicate := by mc_matches

theorem mc_matches_loop_branch (s : State) (h : s.pc = 0x200938) :
    CodeMatchesBlock mc s loop_branch := by mc_matches

/-- Post-pc of `loop_copy_byte`: starting at `0x200914`, the four
    non-branching instructions advance pc by 16 to `0x200924`. -/
private theorem pc_after_loop_copy_byte (s : State) (h : s.pc = 0x200914) :
    (runInstrs s loop_copy_byte).pc = 0x200924 := by
  have h_R := loop_copy_byte_triple s
  simp only [R_loop_copy_byte] at h_R
  rw [h_R.1, h]; decide

/-- Post-pc of `loop_predicate`: starting at `0x200924`, pc advances by
    20 to `0x200938`. -/
private theorem pc_after_loop_predicate (s : State) (h : s.pc = 0x200924) :
    (runInstrs s loop_predicate).pc = 0x200938 := by
  have h_R := loop_predicate_triple s
  simp only [R_loop_predicate] at h_R
  rw [h_R.1, h]; decide

theorem mc_matches_loop_body (s : State) (h : s.pc = 0x200914) :
    CodeMatchesBlock mc s loop_body := by
  unfold loop_body
  apply CodeMatchesBlock_append
  · -- CodeMatchesBlock mc s (loop_copy_byte ++ loop_predicate)
    apply CodeMatchesBlock_append _ _ _ _ (mc_matches_loop_copy_byte s h)
    exact mc_matches_loop_predicate _ (pc_after_loop_copy_byte s h)
  · -- CodeMatchesBlock mc (runInstrs s (loop_copy_byte ++ loop_predicate)) loop_branch
    apply mc_matches_loop_branch
    show (runInstrs s (loop_copy_byte ++ loop_predicate)).pc = 0x200938
    rw [runInstrs_append]
    exact pc_after_loop_predicate _ (pc_after_loop_copy_byte s h)

/-! ## 2. Per-block CFG fragments.

These are the direct lifts of the block triples via `CFG_of_Triple_at`.
Each says: "starting at this block's entry PC, after stepping its
length, the block's `R` holds between entry and reached state." -/

theorem cfg_loop_setup :
    CFG mc (fun s => s.pc = 0x20090c) R_loop_setup :=
  CFG_of_Triple_at 0x20090c loop_setup_triple
    (fun s h => mc_matches_loop_setup s h)

theorem cfg_loop_body :
    CFG mc (fun s => s.pc = 0x200914) R_loop_body :=
  CFG_of_Triple_at 0x200914 loop_body_triple
    (fun s h => mc_matches_loop_body s h)

/-! ## 3. Loop invariant.

Bundles everything we know mid-loop: pc is at the loop-back target,
pointers and counter advanced by `k`, `k` bytes copied so far, plus
the original entry-state preconditions. -/

/-- Loop invariant parameterized by the original entry state `s_entry`
    and the number of completed iterations `k`. -/
def LoopInv (s_entry : State) (k : Nat) (s : State) : Prop :=
  let a0 := getReg s_entry 10
  let a1 := getReg s_entry 11
  let a2 := getReg s_entry 12
  let k_u : UInt32 := k.toUInt32
  s.pc = 0x200914 ∧
  getReg s 10 = a0 ∧
  getReg s 11 = a1 + k_u ∧
  getReg s 12 = a2 - k_u ∧
  getReg s 15 = a1 + k_u + 1 ∧
  getReg s 16 = a0 + k_u ∧
  k ≤ (loop_byte_prefix_count s_entry).toNat ∧
  (∀ i : UInt32, i < k_u → s.mem (a0 + i) = s_entry.mem (a1 + i)) ∧
  (∀ a : UInt32, (∀ i : UInt32, i < k_u → a ≠ a0 + i) → s.mem a = s_entry.mem a) ∧
  Pre_loop_byte_prefix s_entry

/-! ## 4. The three Hoare-loop-rule sub-theorems. -/

/-- **Init**: running `loop_setup` from the loop's entry PC establishes
    `LoopInv` at `k = 0`. -/
theorem loop_inv_init :
    CFG mc
      (fun s => s.pc = 0x20090c ∧ Pre_loop_byte_prefix s)
      (fun s s' => LoopInv s 0 s') := by
  intro s ⟨h_pc, h_pre⟩
  obtain ⟨n, h_R⟩ := cfg_loop_setup s h_pc
  exact ⟨n, by simp_all [R_loop_setup, LoopInv]⟩

/-! ### Shared bound / conversion lemmas for `loop_inv_step` and `loop_inv_exit`. -/

/-- Under `Pre`, `K ≤ 3` (so `K.toNat ≤ 3`). -/
private theorem K_le_3 (s_entry : State) (h_pre : Pre_loop_byte_prefix s_entry) :
    loop_byte_prefix_count s_entry ≤ 3 := by
  obtain ⟨h_align, _, _, _, _⟩ := h_pre
  unfold loop_byte_prefix_count
  bv_decide

/-- Nat counterpart of `K_le_3`. -/
private theorem K_nat_le_3 (s_entry : State) (h_pre : Pre_loop_byte_prefix s_entry) :
    (loop_byte_prefix_count s_entry).toNat ≤ 3 := by
  have h_le := K_le_3 s_entry h_pre
  have h_lt : loop_byte_prefix_count s_entry < 4 := by bv_decide
  have : (loop_byte_prefix_count s_entry).toNat < (4 : UInt32).toNat :=
    UInt32.lt_iff_toNat_lt.mp h_lt
  simp at this; omega

/-- Pumping `k.toUInt32` through `Nat → UInt32` conversion when `k ≤ 2`. -/
@[simp, grind =]
private theorem toUInt32_succ (k : Nat) (h : k ≤ 2) :
    (k + 1).toUInt32 = k.toUInt32 + 1 := by
  match k with
  | 0 | 1 | 2 => rfl
  | (_+3) => omega

/-- `k.toUInt32.toNat = k` for `k ≤ 3` (no UInt32 overflow). -/
@[simp, grind =]
private theorem toUInt32_toNat_eq (k : Nat) (h : k ≤ 3) : k.toUInt32.toNat = k := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | (_+4) => omega

/-- For `K.toNat ≤ 3` and `K ≥ 1`, the UInt32 round-trip
    `(K.toNat - 1).toUInt32 + 1 = K` recovers the original `K`. -/
@[grind =]
private theorem K_minus_1_succ_eq_K (K : UInt32)
    (h_K_nat : K.toNat ≤ 3) (h_K_pos : 0 < K.toNat) :
    (K.toNat - 1).toUInt32 + 1 = K := by
  have h_lhs : ((K.toNat - 1).toUInt32 + 1).toNat = K.toNat := by
    rw [← toUInt32_succ (K.toNat - 1) (by omega)]
    have := toUInt32_toNat_eq (K.toNat - 1 + 1) (by omega)
    omega
  have h_le1 : (K.toNat - 1).toUInt32 + 1 ≤ K := UInt32.le_iff_toNat_le.mpr (by omega)
  have h_le2 : K ≤ (K.toNat - 1).toUInt32 + 1 := UInt32.le_iff_toNat_le.mpr (by omega)
  bv_decide

/-- `(K.toNat - 1).toUInt32 ≤ 2` whenever `K.toNat ≤ 3`. -/
private theorem K_minus_1_uint32_le_2 (K : UInt32) (h_K_nat : K.toNat ≤ 3) :
    (K.toNat - 1).toUInt32 ≤ 2 := by
  have h_kn := toUInt32_toNat_eq (K.toNat - 1) (by omega)
  have h_2 : (2 : UInt32).toNat = 2 := rfl
  exact UInt32.le_iff_toNat_le.mpr (by omega)

/-- `k.toUInt32 ≤ 1` for `k ≤ 1`. -/
private theorem k_toUInt32_le_1 (k : Nat) (h : k ≤ 1) : k.toUInt32 ≤ 1 := by
  match k with | 0 => decide | 1 => decide | (_+2) => omega

/-- From `ku + 1 < K`, `K ≤ a2`, and `ku ≤ 1`: `ku < a2` (UInt32, no wrap). -/
private theorem ku_lt_a2 (ku K a2 : UInt32)
    (h_ku_lt_K : ku + 1 < K) (h_K_le_a2 : K ≤ a2) (h_ku_bound : ku ≤ 1) :
    ku < a2 := by bv_decide

/-- `K = min(K_align, a2) ≤ a2`. -/
private theorem K_le_a2 (s_entry : State) :
    loop_byte_prefix_count s_entry ≤ getReg s_entry 12 := by
  unfold loop_byte_prefix_count
  generalize getReg s_entry 11 = a1
  generalize getReg s_entry 12 = a2
  bv_decide

/-! ### `bv_decide`-discharged facts about the body's continue-flag.

The body computes `a7_fin = ((src+1) &&& 3 != 0) && ((cnt-1) != 0)`.
We characterize each component separately so each `bv_decide` query is
small enough to discharge reliably.  `loop_inv_step` (continue case) uses
both `body_align_ne_zero` and `body_count_ne_zero`; `loop_inv_exit` (exit
case) uses the dual `body_align_or_count_zero` and the loop-post disjunct
`post_aligned_or_zero`. -/

/-- When the next iteration is still below `K`, the alignment test passes. -/
private theorem body_align_ne_zero (a1 a2 ku : UInt32)
    (h_align : a1 &&& 3 ≠ 0) (h_a2_ne : a2 ≠ 0) (h_ku_bound : ku ≤ 1)
    (h_ku_lt_K : ku + 1 <
        (if 4 - (a1 &&& 3) ≤ a2 then 4 - (a1 &&& 3) else a2)) :
    (a1 + ku + 1) &&& 3 ≠ 0 := by bv_decide

/-- When the next iteration is still below `K`, the count test passes. -/
private theorem body_count_ne_zero (a1 a2 ku : UInt32)
    (h_align : a1 &&& 3 ≠ 0) (h_a2_ne : a2 ≠ 0) (h_ku_bound : ku ≤ 1)
    (h_ku_lt_K : ku + 1 <
        (if 4 - (a1 &&& 3) ≤ a2 then 4 - (a1 &&& 3) else a2)) :
    a2 - ku - 1 ≠ 0 := by bv_decide

/-- At the final iteration (`ku + 1 = K`), the body exits:
    alignment OR count test fails. -/
private theorem body_align_or_count_zero (a1 a2 ku : UInt32)
    (h_align : a1 &&& 3 ≠ 0) (h_a2_ne : a2 ≠ 0) (h_ku_bound : ku ≤ 2)
    (h_ku_eq : ku + 1 =
        (if 4 - (a1 &&& 3) ≤ a2 then 4 - (a1 &&& 3) else a2)) :
    (a1 + ku + 1) &&& 3 = 0 ∨ a2 - ku - 1 = 0 := by bv_decide

/-- The loop-exit disjunct in `LoopPost`: after `K` bytes copied,
    either the src pointer is now aligned, or the byte count is exhausted. -/
private theorem post_aligned_or_zero (a1 a2 ku : UInt32)
    (h_align : a1 &&& 3 ≠ 0) (h_a2_ne : a2 ≠ 0) (h_ku_bound : ku ≤ 2)
    (h_ku_eq : ku + 1 =
        (if 4 - (a1 &&& 3) ≤ a2 then 4 - (a1 &&& 3) else a2)) :
    (a1 + (ku + 1)) &&& 3 = 0 ∨ a2 - (ku + 1) = 0 := by bv_decide

/-- **Step**: from a state satisfying `LoopInv` at `k` (with at least
    one more iteration remaining, i.e., `k + 1 < K`), one iteration of
    the loop body brings us back to a state satisfying `LoopInv` at
    `k + 1`.  The body's bne is taken because `k + 1 < K` means the
    continue-flag `a7 ≠ 0`. -/
theorem loop_inv_step (s_entry : State) (k : Nat)
    (h_more : k + 1 < (loop_byte_prefix_count s_entry).toNat) :
    CFG mc
      (LoopInv s_entry k)
      (fun _ s' => LoopInv s_entry (k + 1) s') := by
  intro s h_inv
  obtain ⟨h_pc, h_a0, h_a1, h_a2, h_a5, h_a6, _, h_mem_copied, h_mem_frame, h_pre⟩ := h_inv
  obtain ⟨n, h_R⟩ := cfg_loop_body s h_pc
  refine ⟨n, ?_⟩
  have h_K_nat := K_nat_le_3 _ h_pre
  have h_K_le := K_le_3 _ h_pre
  have h_ku_lt_K : k.toUInt32 + 1 < loop_byte_prefix_count s_entry := by
    rw [← toUInt32_succ k (by omega)]
    have := toUInt32_toNat_eq (k+1) (by omega)
    exact UInt32.lt_iff_toNat_lt.mpr (by omega)
  have h_ku_bound := k_toUInt32_le_1 k (by omega)
  have h_ku_succ : k.toUInt32 + 1 = (k + 1).toUInt32 := (toUInt32_succ k (by omega)).symm
  -- Body continues at iteration k: alignment and count tests both pass.
  have h_taken : (((getReg s 15 &&& 3) != 0) && ((getReg s 12 - 1) != 0)) = true := by
    rw [h_a5, h_a2]
    have h_a := body_align_ne_zero _ _ _ h_pre.1 h_pre.2.1 h_ku_bound h_ku_lt_K
    have h_c := body_count_ne_zero _ _ _ h_pre.1 h_pre.2.1 h_ku_bound h_ku_lt_K
    simp [h_a, h_c]
  -- Discharge LoopInv (k+1).
  simp only [R_loop_body] at h_R
  obtain ⟨h'_pc, h'_11, h'_12, _, _, h'_15, h'_16, _, h'_frame, h'_mem⟩ := h_R
  have h10 : getReg (stepN mc n s) 10 = getReg s 10 :=
    h'_frame ⟨10, by decide⟩ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  -- Bound on the iteration counter inside `a2_entry` (used in the memory proofs).
  have h_ku_lt_a2 : k.toUInt32 < getReg s_entry 12 :=
    ku_lt_a2 _ _ _ h_ku_lt_K (K_le_a2 s_entry) h_ku_bound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_pre⟩
  · rw [h'_pc]; simp [h_taken, h_pc]
  · rw [h10, h_a0]
  · rw [h'_11, h_a1, ← h_ku_succ]; bv_decide
  · rw [h'_12, h_a2, ← h_ku_succ]; bv_decide
  · rw [h'_15, h_a5, ← h_ku_succ]; bv_decide
  · rw [h'_16, h_a6, ← h_ku_succ]; bv_decide
  · omega
  · -- Memory copied: ∀ i < (k+1).toUInt32, s'.mem(a0+i) = s_entry.mem(a1+i)
    intro i hi
    rw [← h_ku_succ] at hi
    have h_i_le : i ≤ k.toUInt32 := by
      revert hi h_ku_bound; generalize k.toUInt32 = ku; intros; bv_decide
    rw [h'_mem, h_a6, h_a1]
    by_cases h_eq : i = k.toUInt32
    · -- i = k.toUInt32: just-written byte.
      rw [h_eq, storeByte_mem_same]
      show s.mem (getReg s_entry 11 + k.toUInt32) = s_entry.mem (getReg s_entry 11 + k.toUInt32)
      -- Use h_mem_frame: the src addr wasn't written by any prior iter (non-aliasing).
      apply h_mem_frame
      intro j hj
      have h_j_lt_a2 : j < getReg s_entry 12 := by
        revert hj h_ku_lt_a2; generalize k.toUInt32 = ku; intros; bv_decide
      exact (h_pre.2.2.1 j k.toUInt32 h_j_lt_a2 h_ku_lt_a2).symm
    · -- i < k.toUInt32: previously-written byte (untouched by this iter's store).
      have h_i_lt : i < k.toUInt32 := by
        revert h_i_le h_eq; intros; bv_decide
      have h_addr_ne : getReg s_entry 10 + i ≠ getReg s_entry 10 + k.toUInt32 := by
        revert h_i_lt h_ku_bound; generalize k.toUInt32 = ku; intros; bv_decide
      rw [storeByte_mem_other _ _ _ _ h_addr_ne]
      exact h_mem_copied i h_i_lt
  · -- Memory frame: ∀ a, (∀ i < (k+1).toUInt32, a ≠ a0+i) → s'.mem a = s_entry.mem a
    intro a h_ne_all
    have h_k_lt_succ : k.toUInt32 < (k + 1).toUInt32 := by rw [← h_ku_succ]; bv_decide
    have h_ne_k : a ≠ getReg s_entry 10 + k.toUInt32 := h_ne_all k.toUInt32 h_k_lt_succ
    rw [h'_mem, h_a6]
    rw [storeByte_mem_other _ _ _ _ h_ne_k]
    apply h_mem_frame
    intro j hj
    have h_j_lt_succ : j < (k + 1).toUInt32 := by
      revert hj h_ku_bound; rw [← h_ku_succ]; generalize k.toUInt32 = ku; intros; bv_decide
    exact h_ne_all j h_j_lt_succ

/-! ## 5. The post-relation (used in `h_exit` and the main theorem). -/

/-- Final post-relation: the loop has exited at `0x200948` with `K` bytes
    copied, pointers advanced, etc. -/
def LoopPost (s s' : State) : Prop :=
  let K := loop_byte_prefix_count s
  let a0 := getReg s 10
  let a1 := getReg s 11
  let a2 := getReg s 12
  s'.pc = 0x200948 ∧
  getReg s' 10 = a0 ∧
  getReg s' 11 = a1 + K ∧
  getReg s' 12 = a2 - K ∧
  getReg s' 16 = a0 + K ∧
  getReg s' 17 = 0 ∧
  (∀ i : UInt32, i < K → s'.mem (a0 + i) = s.mem (a1 + i)) ∧
  (∀ a : UInt32, (∀ i : UInt32, i < K → a ≠ a0 + i) → s'.mem a = s.mem a) ∧
  ((getReg s' 11 &&& 3 = 0) ∨ (getReg s' 12 = 0))

/-- **Exit**: when we've completed `K - 1` iterations, one more
    iteration of the body has `a7 = 0` and the bne falls through to
    `0x200948` (start of B3).  `LoopPost` holds between entry and exit. -/
theorem loop_inv_exit (s_entry : State) (h_K_pos : 0 < (loop_byte_prefix_count s_entry).toNat) :
    CFG mc
      (LoopInv s_entry ((loop_byte_prefix_count s_entry).toNat - 1))
      (fun _ s' => LoopPost s_entry s') := by
  intro s h_inv
  obtain ⟨h_pc, h_a0, h_a1, h_a2, h_a5, h_a6, _, h_mem_copied, h_mem_frame, h_pre⟩ := h_inv
  obtain ⟨n, h_R⟩ := cfg_loop_body s h_pc
  refine ⟨n, ?_⟩
  have h_K_nat := K_nat_le_3 _ h_pre
  have h_ku_eq := K_minus_1_succ_eq_K _ h_K_nat h_K_pos
  have h_ku_bound := K_minus_1_uint32_le_2 _ h_K_nat
  -- Body exits at k = K - 1: alignment OR count test fails.
  have h_not_taken : (((getReg s 15 &&& 3) != 0) && ((getReg s 12 - 1) != 0)) = false := by
    rw [h_a5, h_a2]
    rcases body_align_or_count_zero _ _ _ h_pre.1 h_pre.2.1 h_ku_bound h_ku_eq with h1 | h2
    · simp [h1]
    · simp [h2]
  -- Helper: associativity + `h_ku_eq` collapses `x ± (K-1).toUInt32 ± 1` to `x ± K`.
  have h_add_K : ∀ x : UInt32, x + ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 + 1
                = x + loop_byte_prefix_count s_entry := fun x => by
    have : x + ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 + 1
         = x + (((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 + 1) := by bv_decide
    rw [this, h_ku_eq]
  have h_sub_K : ∀ x : UInt32, x - ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 - 1
                = x - loop_byte_prefix_count s_entry := fun x => by
    have : x - ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 - 1
         = x - (((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 + 1) := by bv_decide
    rw [this, h_ku_eq]
  -- Bound on the iteration counter inside `a2_entry` (used in the memory proofs).
  -- ku + 1 = K (h_ku_eq) and K ≤ a2 (K_le_a2), so ku < a2.
  have h_ku_lt_a2 :
      ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 < getReg s_entry 12 := by
    have h_K_le_a2_inst := K_le_a2 s_entry
    revert h_K_le_a2_inst h_ku_eq h_ku_bound
    generalize ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 = ku
    generalize loop_byte_prefix_count s_entry = K
    generalize getReg s_entry 12 = a2
    intros; bv_decide
  -- Discharge LoopPost.
  simp only [R_loop_body] at h_R
  obtain ⟨h'_pc, h'_11, h'_12, _, _, _, h'_16, h'_17, h'_frame, h'_mem⟩ := h_R
  have h10 : getReg (stepN mc n s) 10 = getReg s 10 :=
    h'_frame ⟨10, by decide⟩ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h'_pc]; simp [h_not_taken, h_pc]
  · rw [h10, h_a0]
  · rw [h'_11, h_a1, h_add_K]
  · rw [h'_12, h_a2, h_sub_K]
  · rw [h'_16, h_a6, h_add_K]
  · rw [h'_17, h_not_taken]; rfl
  · -- Memory copied: ∀ i < K, s'.mem(a0+i) = s_entry.mem(a1+i)
    intro i hi
    -- Convert i < K to i < ku + 1 via h_ku_eq.
    rw [← h_ku_eq] at hi
    have h_i_le : i ≤ ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 := by
      revert hi h_ku_bound
      generalize ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 = ku
      intros; bv_decide
    rw [h'_mem, h_a6, h_a1]
    by_cases h_eq : i = ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32
    · -- i = ku: just-written byte.
      rw [h_eq, storeByte_mem_same]
      show s.mem _ = s_entry.mem _
      apply h_mem_frame
      intro j hj
      have h_j_lt_a2 : j < getReg s_entry 12 := by
        revert hj h_ku_lt_a2
        generalize ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 = ku
        intros; bv_decide
      exact (h_pre.2.2.1 j _ h_j_lt_a2 h_ku_lt_a2).symm
    · -- i < ku: previously-written byte.
      have h_i_lt : i < ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 := by
        revert h_i_le h_eq; intros; bv_decide
      have h_addr_ne :
          getReg s_entry 10 + i ≠
            getReg s_entry 10 + ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 := by
        revert h_i_lt h_ku_bound
        generalize ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 = ku
        intros; bv_decide
      rw [storeByte_mem_other _ _ _ _ h_addr_ne]
      exact h_mem_copied i h_i_lt
  · -- Memory frame: ∀ a, (∀ i < K, a ≠ a0+i) → s'.mem a = s_entry.mem a
    intro a h_ne_all
    have h_ku_lt_K : ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 <
                      loop_byte_prefix_count s_entry := by
      revert h_ku_eq h_ku_bound
      generalize ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 = ku
      generalize loop_byte_prefix_count s_entry = K
      intros; bv_decide
    have h_ne_k : a ≠ getReg s_entry 10 +
                  ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 :=
      h_ne_all _ h_ku_lt_K
    rw [h'_mem, h_a6]
    rw [storeByte_mem_other _ _ _ _ h_ne_k]
    apply h_mem_frame
    intro j hj
    have h_j_lt_K : j < loop_byte_prefix_count s_entry := by
      revert hj h_ku_eq h_ku_bound
      generalize ((loop_byte_prefix_count s_entry).toNat - 1).toUInt32 = ku
      generalize loop_byte_prefix_count s_entry = K
      intros; bv_decide
    exact h_ne_all j h_j_lt_K
  · -- (a1 + K) & 3 = 0 ∨ (a2 - K) = 0
    rw [h'_11, h_a1, h_add_K, h'_12, h_a2, h_sub_K, ← h_ku_eq]
    exact post_aligned_or_zero _ _ _ h_pre.1 h_pre.2.1 h_ku_bound h_ku_eq

/-- Side-condition needed by `CFG.do_while`'s `h_K_pos`: under the
    precondition, `K ≥ 1`. -/
theorem K_pos_of_pre (s : State) (h : s.pc = 0x20090c ∧ Pre_loop_byte_prefix s) :
    0 < (loop_byte_prefix_count s).toNat := by
  obtain ⟨_, h_align, h_a2, _, _, _⟩ := h
  have h_lt : 0 < loop_byte_prefix_count s := by
    unfold loop_byte_prefix_count
    bv_decide
  exact UInt32.lt_iff_toNat_lt.mp h_lt

/-! ## 6. Main theorem: full byte-prefix loop semantics, via `CFG.do_while`.

    The four obligations (init / step / exit / K-pos) are exactly the
    Hoare-while components.  `CFG.do_while` performs the induction over
    `k = 0 .. K-1` internally. -/

theorem byte_prefix_loop_correct :
    CFG mc
      (fun s => s.pc = 0x20090c ∧ Pre_loop_byte_prefix s)
      LoopPost :=
  CFG.do_while
    (K := fun s => (loop_byte_prefix_count s).toNat)
    (Inv := LoopInv)
    loop_inv_init
    loop_inv_step
    loop_inv_exit
    K_pos_of_pre

end MemcpyProof.Hoare
