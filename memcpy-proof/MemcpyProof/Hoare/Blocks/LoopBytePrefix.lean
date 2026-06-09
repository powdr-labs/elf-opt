/-
The byte-prefix loop — the *first* loop in memcpy.

PCs 0x20090c..0x200944.  The loop is encoded as

  * **Setup** (2 instrs, runs once):  `addi a5, a1, 1; addi a6, a0, 0`.
    These establish the invariant `x15 = a1 + 1`, `x16 = a0`.
  * **Main body** (12 instrs, runs every iter):  the byte-copy and the
    two-bit loop predicate computation.
  * **bne a7, zero, -48**: branches back to the start of the main body
    if the loop should continue.

The bne offset is `-48 = -(12 * 4)` bytes, which targets the start of
the main body (not the setup).  Therefore the actual execution is
`setup ++ (main ++ bne) ^ K`, where K is the number of iterations.

We define and prove:
  * `loop_byte_prefix` = `main ++ [bne]` — one full iteration.
  * `R_loop_byte_prefix_one_iter` — its post-condition, parametric in
    entry's `x15` and `x16`.
  * `loop_byte_prefix_one_iter_triple` — the Hoare triple.
  * `loop_byte_prefix_full_run K` = `setup ++ iter^K` — the entire loop.
  * `R_loop_byte_prefix_full` — post-condition of the full loop.
  * `loop_byte_prefix_full_correct` — the loop's correctness theorem.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import MemcpyProof.Hoare.Blocks.BytePrefix
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## The loop list = main body + backward branch.

`main` is the 12 instructions of the loop body that run on every
iteration (i.e. excluding the 2-instr setup that the bne skips). -/

def loop_byte_prefix : List Instr :=
  block_byte_prefix_main ++ [Instr.bne 17 0 0xFFFFFFD0]

/-! ## One-iteration semantics.

After one iteration (main + bne):
  * If `a7_fin ≠ 0` (bne taken), pc = `s.pc` (returns to start of main).
  * If `a7_fin = 0`  (fall through), pc = `s.pc + 52`.

Register and memory effects come straight from `R_block_byte_prefix_main`. -/

def R_loop_byte_prefix_one_iter : State → State → Prop :=
  fun s s' =>
    let a1 := getReg s 11
    let a2 := getReg s 12
    let x15_in := getReg s 15
    let x16_in := getReg s 16
    let a2' : UInt32 := a2 + 0xFFFFFFFF
    let a1_tst : UInt32 := if 0 < (x15_in &&& 3) then 1 else 0
    let a2_tst : UInt32 := if 0 < a2' then 1 else 0
    let a7_fin : UInt32 := a1_tst &&& a2_tst
    s'.pc = (if a7_fin != 0 then s.pc else s.pc + 52) ∧
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

theorem loop_byte_prefix_one_iter_triple :
    Triple loop_byte_prefix R_loop_byte_prefix_one_iter := by
  refine Triple.weaken
    (block_byte_prefix_main_triple.append (Triple_bne 17 0 0xFFFFFFD0)) ?_
  intro s s' h
  obtain ⟨t_main, h_main, h_bne⟩ := h
  simp only [R_block_byte_prefix_main] at h_main
  obtain ⟨hm_pc, hm_11, hm_12, hm_13, hm_14, hm_15, hm_16, hm_17, hm_frame, hm_mem⟩ := h_main
  rw [show getReg t_main 0 = 0 from rfl] at h_bne
  by_cases h_zero : getReg t_main 17 = 0
  · -- BNE NOT TAKEN: a7_fin = 0, s' = advance t_main.
    have hbne' : s' = advance t_main := by
      rw [h_bne, h_zero]; rfl
    subst hbne'
    have h_a7fin :
        (if 0 < ((getReg s 15) &&& 3) then (1 : UInt32) else 0)
          &&& (if 0 < (getReg s 12 + 0xFFFFFFFF) then (1 : UInt32) else 0) = 0 := by
      rw [← hm_17]; exact h_zero
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- pc
      show (advance t_main).pc = if _ != 0 then _ else _
      rw [h_a7fin]
      show (advance t_main).pc = s.pc + 52
      rw [advance_pc, hm_pc]; bv_decide
    · show getReg (advance t_main) 11 = _; rw [getReg_advance]; exact hm_11
    · show getReg (advance t_main) 12 = _; rw [getReg_advance]; exact hm_12
    · show getReg (advance t_main) 13 = _; rw [getReg_advance]; exact hm_13
    · show getReg (advance t_main) 14 = _; rw [getReg_advance]; exact hm_14
    · show getReg (advance t_main) 15 = _; rw [getReg_advance]; exact hm_15
    · show getReg (advance t_main) 16 = _; rw [getReg_advance]; exact hm_16
    · show getReg (advance t_main) 17 = _
      rw [getReg_advance, hm_17, h_a7fin]
    · intro r hr11 hr12 hr13 hr14 hr15 hr16 hr17
      show (advance t_main).regs[r.val] = s.regs[r.val]
      rw [advance_regs]
      exact hm_frame r hr11 hr12 hr13 hr14 hr15 hr16 hr17
    · show (advance t_main).mem = _
      rw [advance_mem, hm_mem]
  · -- BNE TAKEN: a7_fin ≠ 0, s' = jumpTo t_main (t_main.pc + 0xFFFFFFD0).
    have hbne' : s' = jumpTo t_main (t_main.pc + 0xFFFFFFD0) := by
      rw [h_bne]
      have : (getReg t_main 17 != 0) = true := by simp; exact h_zero
      rw [this]; rfl
    subst hbne'
    have h_a7fin_ne :
        ((if 0 < ((getReg s 15) &&& 3) then (1 : UInt32) else 0)
          &&& (if 0 < (getReg s 12 + 0xFFFFFFFF) then (1 : UInt32) else 0)) ≠ 0 := by
      rw [← hm_17]; exact h_zero
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- pc
      show (jumpTo t_main _).pc = if _ != 0 then _ else _
      have h_ne_bool : (((if 0 < ((getReg s 15) &&& 3) then (1 : UInt32) else 0)
            &&& (if 0 < (getReg s 12 + 0xFFFFFFFF) then (1 : UInt32) else 0)) != 0) = true := by
        simp; exact h_a7fin_ne
      rw [h_ne_bool]
      show (jumpTo t_main _).pc = s.pc
      rw [jumpTo_pc, hm_pc]; bv_decide
    · show getReg (jumpTo t_main _) 11 = _; rw [getReg_jumpTo]; exact hm_11
    · show getReg (jumpTo t_main _) 12 = _; rw [getReg_jumpTo]; exact hm_12
    · show getReg (jumpTo t_main _) 13 = _; rw [getReg_jumpTo]; exact hm_13
    · show getReg (jumpTo t_main _) 14 = _; rw [getReg_jumpTo]; exact hm_14
    · show getReg (jumpTo t_main _) 15 = _; rw [getReg_jumpTo]; exact hm_15
    · show getReg (jumpTo t_main _) 16 = _; rw [getReg_jumpTo]; exact hm_16
    · show getReg (jumpTo t_main _) 17 = _
      rw [getReg_jumpTo, hm_17]
    · intro r hr11 hr12 hr13 hr14 hr15 hr16 hr17
      show (jumpTo t_main _).regs[r.val] = s.regs[r.val]
      rw [jumpTo_regs]
      exact hm_frame r hr11 hr12 hr13 hr14 hr15 hr16 hr17
    · show (jumpTo t_main _).mem = _
      rw [jumpTo_mem, hm_mem]

/-! ## Full-loop semantics — `K` derived from the entry state `s`.

The byte-prefix loop runs `K(s)` iterations, where
`K(s) = min(K_align, a2)` with `K_align = 4 - (a1 & 3)`.  The loop only
fires when `a1 & 3 ≠ 0 ∧ a2 ≠ 0`, so `K_align ∈ {1, 2, 3}` and
`K ∈ [1, 3]`.

### Registers after the loop

  **Preserved** (unchanged from `s`):
    x0..x10  — `zero`, `ra`, `sp`, `gp`, `tp`, `t0`, `t1`, `t2`,
               `s0`, `s1`, `a0`           (a0 = the dst base pointer)
    x18..x31 — `s2`..`s11`, `t3`..`t6`

  **Modified to specific values** (read by CFG-successor blocks):
    a1 (x11) = `a1 + K`     -- src pointer advanced
    a2 (x12) = `a2 - K`     -- remaining-bytes count decremented
    a3 (x13) = `a0 + K`     -- read by B3's `andi a1, a3, 3`
    a4 (x14) = `a1 + K`     -- read by B13's `lw a5, 0(a4)`
    a6 (x16) = `a0 + K`     -- new dst pointer
    a7 (x17) = `0`          -- the bne fell through

  **Modified but left unspecified** (overwritten before next use):
    a5 (x15) — reassigned in B4 (`addi a5, zero, 32`).

### Memory after the loop

  * First `K` bytes of dst now equal the corresponding src bytes:
    `Mem'[a0 + i] = Mem[a1 + i]` for all `i < K`.
  * All bytes outside `[a0, a0 + K)` are preserved.
-/

/-- Preconditions for the byte-prefix loop:
    (a) reachability — the CFG routes here only when these hold;
    (b) non-aliasing and no-wraparound — standard memcpy preconditions. -/
def Pre_loop_byte_prefix (s : State) : Prop :=
  let a0 := getReg s 10
  let a1 := getReg s 11
  let a2 := getReg s 12
  (a1 &&& 3) ≠ 0 ∧
  a2 ≠ 0 ∧
  (∀ i j : UInt32, i < a2 → j < a2 → a0 + i ≠ a1 + j) ∧
  a0.toNat + a2.toNat ≤ 2 ^ 32 ∧
  a1.toNat + a2.toNat ≤ 2 ^ 32

/-- `K(s)` — the loop's iteration count, derived from the entry state `s`. -/
def loop_byte_prefix_count (s : State) : UInt32 :=
  let a1 := getReg s 11
  let a2 := getReg s 12
  let K_align : UInt32 := 4 - (a1 &&& 3)
  if K_align ≤ a2 then K_align else a2

/-- `k`-fold concatenation of one iteration (main + bne).  Defined with
    the latest iter at the END to make `Nat.rec` induction natural:
    `iter_n (k+1) = iter_n k ++ loop_byte_prefix`. -/
def loop_byte_prefix_iter_n : Nat → List Instr
  | 0     => []
  | k + 1 => loop_byte_prefix_iter_n k ++ loop_byte_prefix

/-- Full loop execution: 2-instr setup + K iterations of (main + bne). -/
def loop_byte_prefix_full_run (K : Nat) : List Instr :=
  loop_setup ++ loop_byte_prefix_iter_n K

/-- Full-loop post-condition.  No `let`-bindings to avoid whnf
    expansion issues during typechecking. -/
def R_loop_byte_prefix_full : State → State → Prop :=
  fun s s' =>
    Pre_loop_byte_prefix s →
    s'.pc = s.pc + 60 ∧
    getReg s' 17 = 0 ∧
    getReg s' 11 = getReg s 11 + loop_byte_prefix_count s ∧
    getReg s' 12 = getReg s 12 - loop_byte_prefix_count s ∧
    getReg s' 13 = getReg s 10 + loop_byte_prefix_count s ∧
    getReg s' 14 = getReg s 11 + loop_byte_prefix_count s ∧
    getReg s' 16 = getReg s 10 + loop_byte_prefix_count s ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
                   r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
      s'.regs[r.val] = s.regs[r.val]) ∧
    (∀ i : UInt32, i < loop_byte_prefix_count s →
      s'.mem (getReg s 10 + i) = s.mem (getReg s 11 + i)) ∧
    (∀ a : UInt32, (∀ i : UInt32, i < loop_byte_prefix_count s → a ≠ getReg s 10 + i) →
      s'.mem a = s.mem a)

/-! ## Arithmetic helpers for `a7_fin` termination. -/

/-- For K = 1, `a7_fin` (the iter's loop-continue flag computed from
    `x15_in = a1 + 1` and `x12_in - 1`) is zero. -/
private theorem a7_fin_zero_K1 (a1 a2 : UInt32)
    (h_align : a1 &&& 3 ≠ 0) (h_a2 : a2 ≠ 0)
    (h_K1 : (if 4 - (a1 &&& 3) ≤ a2 then 4 - (a1 &&& 3) else a2) = 1) :
    (if 0 < ((a1 + 1) &&& 3) then (1 : UInt32) else 0)
      &&& (if 0 < (a2 + 0xFFFFFFFF) then (1 : UInt32) else 0) = 0 := by
  bv_decide

/-! ## Bounded case analysis on K.

`K = min(4 - (a1 & 3), a2)`.  Under `Pre`, `a1 & 3 ∈ {1, 2, 3}` and
`a2 ≥ 1`, so `K ∈ {1, 2, 3}`.  We prove the loop's correctness by
3-way case split (no induction). -/

/-- `K ∈ {1, 2, 3}` under the precondition. -/
theorem K_cases (s : State) (h_pre : Pre_loop_byte_prefix s) :
    loop_byte_prefix_count s = 1 ∨
    loop_byte_prefix_count s = 2 ∨
    loop_byte_prefix_count s = 3 := by
  obtain ⟨h_align, h_a2, _, _, _⟩ := h_pre
  unfold loop_byte_prefix_count
  bv_decide

/-! ### K = 1 case: loop runs once. -/

/-- For K = 1, the loop runs once and exits.  Given Pre + K = 1,
    after `setup ++ loop_byte_prefix`, the post-conditions of
    `R_loop_byte_prefix_full` hold (specialized to K = 1). -/
theorem loop_K1_correct (s : State) (h_pre : Pre_loop_byte_prefix s)
    (h_K1 : loop_byte_prefix_count s = 1) :
    (runInstrs s (loop_setup ++ loop_byte_prefix)).pc = s.pc + 60 ∧
    getReg (runInstrs s (loop_setup ++ loop_byte_prefix)) 17 = 0 ∧
    getReg (runInstrs s (loop_setup ++ loop_byte_prefix)) 11
      = getReg s 11 + 1 ∧
    getReg (runInstrs s (loop_setup ++ loop_byte_prefix)) 12
      = getReg s 12 - 1 ∧
    getReg (runInstrs s (loop_setup ++ loop_byte_prefix)) 13
      = getReg s 10 + 1 ∧
    getReg (runInstrs s (loop_setup ++ loop_byte_prefix)) 14
      = getReg s 11 + 1 ∧
    getReg (runInstrs s (loop_setup ++ loop_byte_prefix)) 16
      = getReg s 10 + 1 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
                   r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
      (runInstrs s (loop_setup ++ loop_byte_prefix)).regs[r.val]
        = s.regs[r.val]) ∧
    (∀ i : UInt32, i < 1 →
      (runInstrs s (loop_setup ++ loop_byte_prefix)).mem (getReg s 10 + i)
        = s.mem (getReg s 11 + i)) ∧
    (∀ a : UInt32, (∀ i : UInt32, i < 1 → a ≠ getReg s 10 + i) →
      (runInstrs s (loop_setup ++ loop_byte_prefix)).mem a = s.mem a) := by
  -- Compose setup_triple + one_iter_triple.
  have h_R := (loop_setup_triple.append loop_byte_prefix_one_iter_triple) s
  obtain ⟨t_setup, h_setup, h_iter⟩ := h_R
  simp only [R_loop_setup] at h_setup
  simp only [R_loop_byte_prefix_one_iter] at h_iter
  obtain ⟨h_setup_pc, h_setup_15, h_setup_16, h_setup_frame, h_setup_mem⟩ := h_setup
  obtain ⟨h_iter_pc, h_iter_11, h_iter_12, h_iter_13, h_iter_14, _, h_iter_16, h_iter_17,
          h_iter_frame, h_iter_mem⟩ := h_iter
  -- Derive setup-frame facts for the registers iter uses.
  have h_setup_11 : getReg t_setup 11 = getReg s 11 := by
    unfold getReg; rw [if_neg (by decide), if_neg (by decide)]
    exact h_setup_frame ⟨11, by decide⟩ (by decide) (by decide)
  have h_setup_12 : getReg t_setup 12 = getReg s 12 := by
    unfold getReg; rw [if_neg (by decide), if_neg (by decide)]
    exact h_setup_frame ⟨12, by decide⟩ (by decide) (by decide)
  have h_setup_10 : getReg t_setup 10 = getReg s 10 := by
    unfold getReg; rw [if_neg (by decide), if_neg (by decide)]
    exact h_setup_frame ⟨10, by decide⟩ (by decide) (by decide)
  -- Establish a7_fin = 0 for K = 1.
  obtain ⟨h_align, h_a2, _, _, _⟩ := h_pre
  -- Convert h_K1 to a pure if-then-else form (no `let`s).
  have h_K1' : (if 4 - (getReg s 11 &&& 3) ≤ getReg s 12
                then 4 - (getReg s 11 &&& 3)
                else getReg s 12) = 1 := h_K1
  have h_a7_zero :
      (if 0 < ((getReg t_setup 15) &&& 3) then (1 : UInt32) else 0)
        &&& (if 0 < (getReg t_setup 12 + 0xFFFFFFFF) then (1 : UInt32) else 0) = 0 := by
    rw [h_setup_15, h_setup_12]
    exact a7_fin_zero_K1 _ _ h_align h_a2 h_K1'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pc = s.pc + 60
    rw [h_iter_pc, h_a7_zero]
    show t_setup.pc + 52 = s.pc + 60
    rw [h_setup_pc]; bv_decide
  · -- x17 = 0
    rw [h_iter_17]; exact h_a7_zero
  · -- x11 = a1 + 1
    rw [h_iter_11, h_setup_11]
  · -- x12 = a2 - 1
    rw [h_iter_12, h_setup_12]; bv_decide
  · -- x13 = a0 + 1
    rw [h_iter_13, h_setup_16]
  · -- x14 = a1 + 1
    rw [h_iter_14, h_setup_11]
  · -- x16 = a0 + 1
    rw [h_iter_16, h_setup_16]
  · -- frame
    intro r hr11 hr12 hr13 hr14 hr15 hr16 hr17
    -- After iter, regs[r] = t_setup.regs[r]; after setup, t_setup.regs[r] = s.regs[r].
    have h1 : (runInstrs s (loop_setup ++ loop_byte_prefix)).regs[r.val]
            = t_setup.regs[r.val] :=
      h_iter_frame r hr11 hr12 hr13 hr14 hr15 hr16 hr17
    have h2 : t_setup.regs[r.val] = s.regs[r.val] :=
      h_setup_frame r hr15 hr16
    rw [h1, h2]
  · -- mem: ∀ i < 1, s'.mem (a0 + i) = s.mem (a1 + i). Only i = 0.
    intro i hi
    have h_i_zero : i = 0 := by bv_decide
    subst h_i_zero
    have h_add0_10 : getReg s 10 + 0 = getReg s 10 := by bv_decide
    have h_add0_11 : getReg s 11 + 0 = getReg s 11 := by bv_decide
    rw [h_add0_10, h_add0_11, h_iter_mem, h_setup_16, h_setup_11, h_setup_mem]
    unfold storeByte
    simp
  · -- untouched: ∀ a, (∀ i < 1, a ≠ a0 + i) → s'.mem a = s.mem a.
    intro a h_ne
    have h_a_ne : a ≠ getReg s 10 := by
      have h0 := h_ne 0 (by bv_decide)
      have h_add0 : getReg s 10 + 0 = getReg s 10 := by bv_decide
      rwa [h_add0] at h0
    rw [h_iter_mem, h_setup_16, h_setup_11]
    unfold storeByte
    show (if a == getReg s 10 then t_setup.mem (getReg s 11) else t_setup.mem a) = s.mem a
    simp [h_a_ne, h_setup_mem]

/-! ### K = 2 case (placeholder).

  The proof follows the same pattern as `loop_K1_correct`:
  - Apply `setup_triple.append (one_iter_triple.append one_iter_triple)`.
  - Destructure to get `t1` (post-setup) and `t2` (post-iter-1).
  - Use a `a7_fin_step_K2` helper: at iter 1, `a7_fin = 1`; at iter 2, `a7_fin = 0`.
  - For the memory conjunct at i = 1, use `Pre`'s non-aliasing: the byte
    `t2.mem (a1 + 1)` equals `s.mem (a1 + 1)` (since iter 1 only writes
    at `a0`, and `a0 ≠ a1 + 1` by non-aliasing). -/
theorem loop_K2_correct (s : State) (h_pre : Pre_loop_byte_prefix s)
    (h_K2 : loop_byte_prefix_count s = 2) :
    (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))).pc
      = s.pc + 60 ∧
    getReg (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))) 17 = 0 ∧
    getReg (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))) 11
      = getReg s 11 + 2 ∧
    getReg (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))) 12
      = getReg s 12 - 2 ∧
    getReg (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))) 13
      = getReg s 10 + 2 ∧
    getReg (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))) 14
      = getReg s 11 + 2 ∧
    getReg (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))) 16
      = getReg s 10 + 2 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
                   r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
      (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))).regs[r.val]
        = s.regs[r.val]) ∧
    (∀ i : UInt32, i < 2 →
      (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))).mem
        (getReg s 10 + i) = s.mem (getReg s 11 + i)) ∧
    (∀ a : UInt32, (∀ i : UInt32, i < 2 → a ≠ getReg s 10 + i) →
      (runInstrs s (loop_setup ++ (loop_byte_prefix ++ loop_byte_prefix))).mem a
        = s.mem a) := by
  sorry

/-! ### K = 3 case (placeholder). -/
theorem loop_K3_correct (s : State) (h_pre : Pre_loop_byte_prefix s)
    (h_K3 : loop_byte_prefix_count s = 3) :
    (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))).pc
      = s.pc + 60 ∧
    getReg (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))) 17 = 0 ∧
    getReg (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))) 11
      = getReg s 11 + 3 ∧
    getReg (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))) 12
      = getReg s 12 - 3 ∧
    getReg (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))) 13
      = getReg s 10 + 3 ∧
    getReg (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))) 14
      = getReg s 11 + 3 ∧
    getReg (runInstrs s
      (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))) 16
      = getReg s 10 + 3 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
                   r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
      (runInstrs s
        (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))).regs[r.val]
        = s.regs[r.val]) ∧
    (∀ i : UInt32, i < 3 →
      (runInstrs s
        (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))).mem
        (getReg s 10 + i) = s.mem (getReg s 11 + i)) ∧
    (∀ a : UInt32, (∀ i : UInt32, i < 3 → a ≠ getReg s 10 + i) →
      (runInstrs s
        (loop_setup ++ ((loop_byte_prefix ++ loop_byte_prefix) ++ loop_byte_prefix))).mem a
        = s.mem a) := by
  sorry

set_option maxHeartbeats 2000000 in
/-- Full-loop correctness — by 3-way case split on K ∈ {1, 2, 3}. -/
theorem loop_byte_prefix_full_correct (s : State) :
    R_loop_byte_prefix_full s
      (runInstrs s (loop_byte_prefix_full_run (loop_byte_prefix_count s).toNat)) := by
  intro h_pre
  rcases K_cases s h_pre with h_K1 | h_K2 | h_K3
  · -- K = 1
    have h_eq : loop_byte_prefix_full_run (loop_byte_prefix_count s).toNat
              = loop_setup ++ loop_byte_prefix := by
      rw [h_K1]; rfl
    rw [h_eq, h_K1]
    exact loop_K1_correct s h_pre h_K1
  · -- K = 2 wire-up: hits whnf timeout even at 8M heartbeats, likely
    -- a longer-list reduction issue.  loop_K2_correct itself is sorried.
    sorry
  · -- K = 3 wire-up: same issue.  loop_K3_correct itself is sorried.
    sorry

end MemcpyProof.Hoare
