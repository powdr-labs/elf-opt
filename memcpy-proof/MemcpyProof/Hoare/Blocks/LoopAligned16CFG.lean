/-
CFG-level semantics of the aligned 16-byte main loop (B13's setup + B14 + bltu).

The "fast path" of memcpy: when src is word-aligned and `≥ 16` bytes
remain, this loop copies 16 bytes per iteration via 4 word-loads + 4
word-stores, decrementing `a2` by 16 each time.  The loop exits via a
bltu (a1 < a2) where `a1 = 15` and `a2` is the remaining byte count.

Layout:
  0x200a18  block_F_first's setup: addi a1, zero, 15  (1 instr; runs once)
  0x200a1c  block_F_iter (B14, 11 instrs)             ← loop-back target
  0x200a48  bltu a1, a2, -44                          (back-edge)
  0x200a4c  fall-through (B15)
-/

import MemcpyProof.Hoare.Blocks.LoopBytePrefixCFG  -- for `mc` and other shared utilities
import MemcpyProof.Hoare.Blocks.AlignedLoop
import MemcpyProof.Extract

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## 0. Loop precondition and iteration count.

The loop runs only when `a2 ≥ 16` (the caller dispatches to a shorter
tail path if not).  It also needs `src` (a4) word-aligned and the
standard non-aliasing / no-wrap preconditions. -/

def Pre_aligned16_loop (s : State) : Prop :=
  let dst := getReg s 13
  let src := getReg s 14
  let len := getReg s 12
  16 ≤ len ∧
  (src &&& 3) = 0 ∧
  (dst &&& 3) = 0 ∧
  (∀ i j : UInt32, i < len → j < len → dst + i ≠ src + j) ∧
  dst.toNat + len.toNat ≤ 2 ^ 32 ∧
  src.toNat + len.toNat ≤ 2 ^ 32

/-- `K(s)` — number of iterations, equal to `len / 16`. -/
def aligned16_loop_count (s : State) : UInt32 :=
  getReg s 12 / 16

/-! ## 1. The loop body's block + Triple.

`block_F_iter` is the 11-instr body (defined in `AlignedLoop.lean`).
We append the bltu to get the full body of the do-while loop. -/

/-- Body = 11-instr aligned-copy + bltu back-edge. -/
def aligned16_body : List Instr := block_F_iter ++ [Instr.bltu 11 12 0xFFFFFFD4]

/-- Post-relation of the body (B14 + bltu): registers updated by 16 each,
    pc dispatches based on `a1 < len_post` (bltu's condition). -/
def R_aligned16_body : State → State → Prop :=
  fun s s' =>
    let dst := getReg s 13
    let src := getReg s 14
    let len := getReg s 12
    let len_post : UInt32 := len + 0xFFFFFFF0  -- = len - 16
    let taken : Bool := getReg s 11 < len_post
    -- After 11 instrs of body, pc = s.pc + 44.  After bltu:
    --   taken: pc = (s.pc + 44) + 0xFFFFFFD4 = s.pc (back-edge).
    --   else:  pc = (s.pc + 44) + 4         = s.pc + 48 (fall-through).
    s'.pc = (if taken then s.pc else s.pc + 48) ∧
    getReg s' 11 = getReg s 11 ∧
    getReg s' 12 = len_post ∧
    getReg s' 13 = dst + 16 ∧
    getReg s' 14 = src + 16 ∧
    (∀ r : Fin 32, r.val ≠ 5 → r.val ≠ 11 → r.val ≠ 12 → r.val ≠ 13 → r.val ≠ 14 →
                   r.val ≠ 15 → r.val ≠ 16 → r.val ≠ 17 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord (storeWord (storeWord (storeWord s
                dst (loadWord s src))
                (dst + 4) (loadWord s (src + 4)))
                (dst + 8) (loadWord s (src + 8)))
                (dst + 12) (loadWord s (src + 12))).mem

theorem aligned16_body_triple : Triple aligned16_body R_aligned16_body := by
  refine Triple.weaken (block_F_iter_triple.append (Triple_bltu 11 12 0xFFFFFFD4)) ?_
  rintro s s' ⟨t, h_iter, h_bltu⟩
  simp only [R_block_F_iter] at h_iter
  obtain ⟨h_i_pc, h_i_11, h_i_12, h_i_13, h_i_14, h_i_frame, h_i_mem⟩ := h_iter
  -- Derive `t.regs[11] = s.regs[11]` for use in jumpTo/advance regs lookups.
  have ht_11 : t.regs[11] = s.regs[11] := by
    have h := h_i_11
    unfold getReg at h
    rw [if_neg (by decide), if_neg (by decide)] at h
    exact h
  -- Case on bltu's branch (equivalent: a1=getReg s 11 < a2_post=getReg s 12 + 0xFFFFFFF0).
  by_cases h_taken : getReg t 11 < getReg t 12
  · -- bltu taken: s' = jumpTo t _.
    have hs' : s' = jumpTo t (t.pc + 0xFFFFFFD4) := by rw [h_bltu]; rw [if_pos h_taken]
    have h_taken' : getReg s 11 < getReg s 12 + 0xFFFFFFF0 := by
      rw [← h_i_11, ← h_i_12]; exact h_taken
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s'.pc = if _ then _ else _
      rw [if_pos (by simpa using h_taken'), hs', jumpTo_pc, h_i_pc]; bv_decide
    · rw [hs', getReg_jumpTo]; exact h_i_11
    · rw [hs', getReg_jumpTo]; exact h_i_12
    · rw [hs', getReg_jumpTo]; exact h_i_13
    · rw [hs', getReg_jumpTo]; exact h_i_14
    · intro r h5 h11 h12 h13 h14 h15 h16 h17
      rw [hs', jumpTo_regs]
      exact h_i_frame r h5 h12 h13 h14 h15 h16 h17
    · rw [hs', jumpTo_mem]; exact h_i_mem
  · -- bltu not taken: s' = advance t.
    have hs' : s' = advance t := by rw [h_bltu]; rw [if_neg h_taken]
    have h_not_taken' : ¬ (getReg s 11 < getReg s 12 + 0xFFFFFFF0) := by
      rw [← h_i_11, ← h_i_12]; exact h_taken
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s'.pc = if _ then _ else _
      rw [if_neg (by simpa using h_not_taken'), hs', advance_pc, h_i_pc]; bv_decide
    · rw [hs', getReg_advance]; exact h_i_11
    · rw [hs', getReg_advance]; exact h_i_12
    · rw [hs', getReg_advance]; exact h_i_13
    · rw [hs', getReg_advance]; exact h_i_14
    · intro r h5 h11 h12 h13 h14 h15 h16 h17
      rw [hs', advance_regs]
      exact h_i_frame r h5 h12 h13 h14 h15 h16 h17
    · rw [hs', advance_mem]; exact h_i_mem

/-! ## 2. Code-match lemmas. -/

theorem mc_matches_block_F_first_setup (s : State) (h : s.pc = 0x200a18) :
    CodeMatchesBlock mc s [Instr.addi 11 0 15] := by mc_matches

theorem mc_matches_aligned16_body (s : State) (h : s.pc = 0x200a1c) :
    CodeMatchesBlock mc s aligned16_body := by mc_matches

/-! ## 3. Per-block CFG fragments. -/

theorem cfg_block_F_first_setup :
    CFG mc (fun s => s.pc = 0x200a18)
      (fun s s' => s' = advance (setReg s 11 (getReg s 0 + 15))) :=
  CFG_of_Triple_at 0x200a18 (Triple_addi 11 0 15)
    (fun s h => mc_matches_block_F_first_setup s h)

theorem cfg_aligned16_body :
    CFG mc (fun s => s.pc = 0x200a1c) R_aligned16_body :=
  CFG_of_Triple_at 0x200a1c aligned16_body_triple
    (fun s h => mc_matches_aligned16_body s h)

/-! ## 4. Loop invariant. -/

/-- Loop invariant: after `k` iterations, `16*k` bytes copied, pointers
    advanced, `a1 = 15`, `len` decremented by `16*k`.

    Arithmetic stated in `Nat`.  Pointer values use `% 2^32` to handle
    the (edge) case where `dst + 16K = 2^32` exactly — UInt32 wraps to
    0 then, and Nat addition would over-state by `2^32`. -/
def LoopInv_aligned16 (s_entry : State) (k : Nat) (s : State) : Prop :=
  let dst := (getReg s_entry 13).toNat
  let src := (getReg s_entry 14).toNat
  let len := (getReg s_entry 12).toNat
  s.pc = 0x200a1c ∧
  getReg s 11 = 15 ∧
  (getReg s 12).toNat = len - 16 * k ∧
  (getReg s 13).toNat = (dst + 16 * k) % 2 ^ 32 ∧
  (getReg s 14).toNat = (src + 16 * k) % 2 ^ 32 ∧
  k ≤ (aligned16_loop_count s_entry).toNat ∧
  -- Words copied so far: for each word-index w < 4*k, dst[dst + 4w] = src[src + 4w].
  (∀ w < 4 * k,
    loadWord s (dst + 4 * w).toUInt32 = loadWord s_entry (src + 4 * w).toUInt32) ∧
  (∀ a : Nat, (∀ w < 4 * k,
                    ∀ b < 4, a.toUInt32 ≠ (dst + 4 * w + b).toUInt32) →
    s.mem a.toUInt32 = s_entry.mem a.toUInt32) ∧
  Pre_aligned16_loop s_entry

/-! ## 5. Loop sub-theorems.

These are the four obligations of `CFG.do_while`.  The proofs use
`omega` on Nat invariants instead of `bv_decide` on UInt32. -/

def LoopPost_aligned16 (s s' : State) : Prop :=
  let K := (aligned16_loop_count s).toNat
  let dst := (getReg s 13).toNat
  let src := (getReg s 14).toNat
  let len := (getReg s 12).toNat
  s'.pc = 0x200a4c ∧
  getReg s' 11 = 15 ∧
  (getReg s' 12).toNat = len - 16 * K ∧
  (getReg s' 13).toNat = (dst + 16 * K) % 2 ^ 32 ∧
  (getReg s' 14).toNat = (src + 16 * K) % 2 ^ 32 ∧
  -- 16*K bytes copied (expressed at word granularity).
  (∀ w < 4 * K,
    loadWord s' (dst + 4 * w).toUInt32 = loadWord s (src + 4 * w).toUInt32) ∧
  -- Frame: bytes outside the copied window untouched.
  (∀ a : Nat, (∀ w < 4 * K,
                    ∀ b < 4, a.toUInt32 ≠ (dst + 4 * w + b).toUInt32) →
    s'.mem a.toUInt32 = s.mem a.toUInt32) ∧
  -- len < 16 after the loop (the exit condition).
  getReg s' 12 < 16

theorem loop_inv_init_aligned16 :
    CFG mc
      (fun s => s.pc = 0x200a18 ∧ Pre_aligned16_loop s)
      (fun s s' => LoopInv_aligned16 s 0 s') := by
  intro s ⟨h_pc, h_pre⟩
  obtain ⟨n, h_R⟩ := cfg_block_F_first_setup s h_pc
  exact ⟨n, by simp_all [LoopInv_aligned16]⟩

/-! ### Helpers for the step/exit proofs.

All arithmetic at the invariant level stays in `Nat`; UInt32 arithmetic
is only used to read the body's `R_aligned16_body`, then bridged back
to `Nat` via `.toNat`. -/

/-- Pointer increment: `(a + 16 : UInt32).toNat = (a.toNat + 16) % 2^32`. -/
private theorem ptr_add_16_toNat (a : UInt32) :
    (a + 16).toNat = (a.toNat + 16) % 2 ^ 32 := by
  rw [UInt32.toNat_add]; rfl

/-- Byte-count decrement: `(a + 0xFFFFFFF0 : UInt32).toNat = a.toNat - 16`
    when `a.toNat ≥ 16` (no UInt32 wraparound on the subtraction). -/
private theorem ptr_sub_16_toNat (a : UInt32) (h : a.toNat ≥ 16) :
    (a + 0xFFFFFFF0).toNat = a.toNat - 16 := by
  rw [UInt32.toNat_add]
  show (a.toNat + 4294967280) % 2 ^ 32 = a.toNat - 16
  have := a.toNat_lt; omega

/-- `K.toNat * 16 ≤ len.toNat` — the loop consumes a multiple of 16. -/
private theorem K_times_16_le_len (s_entry : State) :
    (aligned16_loop_count s_entry).toNat * 16 ≤ (getReg s_entry 12).toNat := by
  show (getReg s_entry 12).toNat / 16 * 16 ≤ (getReg s_entry 12).toNat
  omega

/-- The exit tail: `len.toNat - K.toNat * 16 < 16`. -/
private theorem len_minus_K16_lt_16 (s_entry : State) :
    (getReg s_entry 12).toNat - (aligned16_loop_count s_entry).toNat * 16 < 16 := by
  show (getReg s_entry 12).toNat - (getReg s_entry 12).toNat / 16 * 16 < 16
  omega

/-- Two `UInt32`s with equal `.toNat` are equal. -/
private theorem UInt32_eq_of_toNat_eq (a b : UInt32) (h : a.toNat = b.toNat) : a = b := by
  have h1 : a ≤ b := UInt32.le_iff_toNat_le.mpr (Nat.le_of_eq h)
  have h2 : b ≤ a := UInt32.le_iff_toNat_le.mpr (Nat.le_of_eq h.symm)
  exact UInt32.le_antisymm h1 h2

/-- The body's 4 word-stores at `dst_curr, dst_curr+4/8/12` preserve memory at any
    address `a` that differs from all 16 stored byte addresses. -/
private theorem aligned16_body_mem_outside
    (s : State) (a : UInt32) (dst_curr src_curr : UInt32)
    (h : ∀ i : UInt32, i < 16 → a ≠ dst_curr + i) :
    (storeWord (storeWord (storeWord (storeWord s
                dst_curr (loadWord s src_curr))
                (dst_curr + 4) (loadWord s (src_curr + 4)))
                (dst_curr + 8) (loadWord s (src_curr + 8)))
                (dst_curr + 12) (loadWord s (src_curr + 12))).mem a = s.mem a := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide)
  have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  have h8 := h 8 (by decide); have h9 := h 9 (by decide)
  have h10 := h 10 (by decide); have h11 := h 11 (by decide)
  have h12 := h 12 (by decide); have h13 := h 13 (by decide)
  have h14 := h 14 (by decide); have h15 := h 15 (by decide)
  rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]

/-- The body's effect on `(getReg s 13 + i).toNat` in terms of the entry-state
    `dst.toNat + 16k + i.toNat`. -/
private theorem getReg_13_plus_toNat
    (s_entry s : State) (k : Nat) (i : UInt32)
    (h_13 : (getReg s 13).toNat = ((getReg s_entry 13).toNat + 16 * k) % 2 ^ 32) :
    (getReg s 13 + i).toNat = ((getReg s_entry 13).toNat + 16 * k + i.toNat) % 2 ^ 32 := by
  rw [UInt32.toNat_add, h_13]; omega

/-- `loadWord` depends only on `.mem`. -/
private theorem loadWord_of_mem_eq {s s' : State} (h : s.mem = s'.mem) (a : UInt32) :
    loadWord s a = loadWord s' a := by
  unfold loadWord loadByte
  rw [h]

/-- `loadWord` at the just-stored address recovers the stored value. -/
private theorem loadWord_storeWord_same (s : State) (a v : UInt32) :
    loadWord (storeWord s a v) a = v := by
  unfold loadWord loadByte
  rw [show (storeWord s a v).mem a = v.toUInt8 from by
        have := storeWord_mem_byte s a v 0 (by decide); simpa using this,
      show (storeWord s a v).mem (a + 1) = (v >>> 8).toUInt8 from
        storeWord_mem_byte s a v 1 (by decide),
      show (storeWord s a v).mem (a + 2) = (v >>> 16).toUInt8 from
        storeWord_mem_byte s a v 2 (by decide),
      show (storeWord s a v).mem (a + 3) = (v >>> 24).toUInt8 from
        storeWord_mem_byte s a v 3 (by decide)]
  bv_decide

/-- A previously-copied byte address is strictly below the body's write range
    `[dst_curr, dst_curr + 16)`, so it's outside.
    Requires `k+1 ≤ K` so that the body's write range stays within `[0, 2^32)`. -/
private theorem step_case1_byte_outside
    (s_entry s : State) (k : Nat)
    (h_pre : Pre_aligned16_loop s_entry)
    (h_13 : (getReg s 13).toNat = ((getReg s_entry 13).toNat + 16 * k) % 2 ^ 32)
    (h_k1_le : k + 1 ≤ (aligned16_loop_count s_entry).toNat)
    (w : Nat) (h_w : w < 4 * k)
    (offset : UInt32) (h_off : offset.toNat < 4) :
    ∀ i : UInt32, i < 16 →
      ((getReg s_entry 13).toNat + 4 * w : Nat).toUInt32 + offset ≠ getReg s 13 + i := by
  intro i hi h_eq
  have h_toUInt32_toNat : (Nat.toUInt32 ((getReg s_entry 13).toNat + 4 * w)).toNat
                        = ((getReg s_entry 13).toNat + 4 * w) % 2 ^ 32 := by
    show (BitVec.ofNat 32 _).toNat = _
    simp [BitVec.toNat_ofNat]
  have h_nat_eq :
      (((getReg s_entry 13).toNat + 4 * w) % 2 ^ 32 + offset.toNat) % 2 ^ 32
      = ((getReg s_entry 13).toNat + 16 * k + i.toNat) % 2 ^ 32 := by
    have := congrArg UInt32.toNat h_eq
    rw [UInt32.toNat_add, UInt32.toNat_add, h_13, h_toUInt32_toNat] at this
    omega
  have h_K_le_len := K_times_16_le_len s_entry
  have h_no_wrap : (getReg s_entry 13).toNat + (getReg s_entry 12).toNat ≤ 2 ^ 32 :=
    h_pre.2.2.2.2.1
  have hi_nat : i.toNat < 16 := by
    have := UInt32.lt_iff_toNat_lt.mp hi; simpa using this
  omega

/-- `loadWord` at the `j`-th stored offset in the body's chain (j ∈ {0..3}). -/
private theorem aligned16_body_loadWord_at_offset
    (s : State) (dst_curr src_curr : UInt32) (j : UInt32) (h : j < 4) :
    loadWord (storeWord (storeWord (storeWord (storeWord s
                dst_curr (loadWord s src_curr))
                (dst_curr + 4) (loadWord s (src_curr + 4)))
                (dst_curr + 8) (loadWord s (src_curr + 8)))
                (dst_curr + 12) (loadWord s (src_curr + 12))) (dst_curr + 4 * j)
    = loadWord s (src_curr + 4 * j) := by
  rcases (by bv_decide : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · -- j = 0: peel 3 outer storeWords at offsets 4/8/12.
    rw [show dst_curr + 4 * 0 = dst_curr from by bv_decide,
        show src_curr + 4 * 0 = src_curr from by bv_decide]
    have hb : ∀ b : UInt32, b < 4 →
        (storeWord (storeWord (storeWord (storeWord s
                    dst_curr (loadWord s src_curr))
                    (dst_curr + 4) (loadWord s (src_curr + 4)))
                    (dst_curr + 8) (loadWord s (src_curr + 8)))
                    (dst_curr + 12) (loadWord s (src_curr + 12))).mem (dst_curr + b)
              = (storeWord s dst_curr (loadWord s src_curr)).mem (dst_curr + b) := by
      intro b hb
      rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
      rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
      rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
    apply loadWord_eq_of_bytes_eq _ _ dst_curr dst_curr
      (show _ = _ by have := hb 0 (by decide); simpa using this)
      (hb 1 (by decide)) (hb 2 (by decide)) (hb 3 (by decide))
      |>.trans
    exact loadWord_storeWord_same s dst_curr (loadWord s src_curr)
  · -- j = 1: peel 2 outer storeWords (at 8/12), then 1 inner (at 0).
    rw [show dst_curr + 4 * 1 = dst_curr + 4 from by bv_decide,
        show src_curr + 4 * 1 = src_curr + 4 from by bv_decide]
    have hb : ∀ b : UInt32, b < 4 →
        (storeWord (storeWord (storeWord (storeWord s
                    dst_curr (loadWord s src_curr))
                    (dst_curr + 4) (loadWord s (src_curr + 4)))
                    (dst_curr + 8) (loadWord s (src_curr + 8)))
                    (dst_curr + 12) (loadWord s (src_curr + 12))).mem (dst_curr + 4 + b)
              = (storeWord (storeWord s
                    dst_curr (loadWord s src_curr))
                    (dst_curr + 4) (loadWord s (src_curr + 4))).mem (dst_curr + 4 + b) := by
      intro b hb
      rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
      rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
    apply loadWord_eq_of_bytes_eq _ _ (dst_curr + 4) (dst_curr + 4)
      (show _ = _ by have := hb 0 (by decide); simpa using this)
      (hb 1 (by decide)) (hb 2 (by decide)) (hb 3 (by decide))
      |>.trans
    exact loadWord_storeWord_same _ (dst_curr + 4) (loadWord s (src_curr + 4))
  · -- j = 2.
    rw [show dst_curr + 4 * 2 = dst_curr + 8 from by bv_decide,
        show src_curr + 4 * 2 = src_curr + 8 from by bv_decide]
    have hb : ∀ b : UInt32, b < 4 →
        (storeWord (storeWord (storeWord (storeWord s
                    dst_curr (loadWord s src_curr))
                    (dst_curr + 4) (loadWord s (src_curr + 4)))
                    (dst_curr + 8) (loadWord s (src_curr + 8)))
                    (dst_curr + 12) (loadWord s (src_curr + 12))).mem (dst_curr + 8 + b)
              = (storeWord (storeWord (storeWord s
                    dst_curr (loadWord s src_curr))
                    (dst_curr + 4) (loadWord s (src_curr + 4)))
                    (dst_curr + 8) (loadWord s (src_curr + 8))).mem (dst_curr + 8 + b) := by
      intro b hb
      rw [storeWord_mem_other _ _ _ _ (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
    apply loadWord_eq_of_bytes_eq _ _ (dst_curr + 8) (dst_curr + 8)
      (show _ = _ by have := hb 0 (by decide); simpa using this)
      (hb 1 (by decide)) (hb 2 (by decide)) (hb 3 (by decide))
      |>.trans
    exact loadWord_storeWord_same _ (dst_curr + 8) (loadWord s (src_curr + 8))
  · -- j = 3: outermost storeWord, no peeling needed.
    rw [show dst_curr + 4 * 3 = dst_curr + 12 from by bv_decide,
        show src_curr + 4 * 3 = src_curr + 12 from by bv_decide]
    exact loadWord_storeWord_same _ (dst_curr + 12) (loadWord s (src_curr + 12))

theorem loop_inv_step_aligned16 (s_entry : State) (k : Nat)
    (h_more : k + 1 < (aligned16_loop_count s_entry).toNat) :
    CFG mc
      (LoopInv_aligned16 s_entry k)
      (fun _ s' => LoopInv_aligned16 s_entry (k + 1) s') := by
  intro s h_inv
  obtain ⟨h_pc, h_11, h_12, h_13, h_14, h_k_le, h_mem_copied, h_mem_frame, h_pre⟩ := h_inv
  obtain ⟨n, h_R⟩ := cfg_aligned16_body s h_pc
  refine ⟨n, ?_⟩
  simp only [R_aligned16_body] at h_R
  obtain ⟨h'_pc, h'_11, h'_12, h'_13, h'_14, h'_frame, h'_mem⟩ := h_R
  have h_K_le_len := K_times_16_le_len s_entry
  -- Byte counter ≥ 16: we have at least one more iter to go.
  have h_12_ge_16 : (getReg s 12).toNat ≥ 16 := by rw [h_12]; omega
  -- bltu taken: 15 < (a2 - 16).toNat = (a2 - 16) since a2 ≥ 16.
  have h_taken : (getReg s 11 < getReg s 12 + 0xFFFFFFF0) = true := by
    have h_lt : (getReg s 11).toNat < (getReg s 12 + 0xFFFFFFF0).toNat := by
      rw [h_11, ptr_sub_16_toNat _ h_12_ge_16]; show 15 < _; omega
    simp [UInt32.lt_iff_toNat_lt.mpr h_lt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_pre⟩
  · rw [h'_pc]; simp [h_taken, h_pc]
  · rw [h'_11]; exact h_11
  · rw [h'_12, ptr_sub_16_toNat _ h_12_ge_16, h_12]; omega
  · rw [h'_13, ptr_add_16_toNat, h_13]; omega
  · rw [h'_14, ptr_add_16_toNat, h_14]; omega
  · omega
  · -- Memory copied.
    intro w hw
    by_cases h_case : w < 4 * k
    · -- Case 1: previously copied. Body's stores don't touch (dst + 4w + b).
      have h_k1_le : k + 1 ≤ (aligned16_loop_count s_entry).toNat := by omega
      apply Eq.trans _ (h_mem_copied w h_case)
      apply loadWord_eq_of_bytes_eq
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        have h := step_case1_byte_outside s_entry s k h_pre h_13 h_k1_le w h_case 0 (by decide) i hi
        simpa using h
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        exact step_case1_byte_outside s_entry s k h_pre h_13 h_k1_le w h_case 1 (by decide) i hi
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        exact step_case1_byte_outside s_entry s k h_pre h_13 h_k1_le w h_case 2 (by decide) i hi
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        exact step_case1_byte_outside s_entry s k h_pre h_13 h_k1_le w h_case 3 (by decide) i hi
    · -- Case 2: newly stored. w = 4*k + j_nat for j_nat ∈ {0..3}.
      have h_w_ge : 4 * k ≤ w := by omega
      have h_j_lt_nat : w - 4 * k < 4 := by omega
      let j : UInt32 := (w - 4 * k).toUInt32
      have h_j_toNat : j.toNat = w - 4 * k := by
        show (BitVec.ofNat 32 _).toNat = _
        simp [BitVec.toNat_ofNat]; omega
      have h_j_lt_uint : j < 4 := by
        apply UInt32.lt_iff_toNat_lt.mpr
        rw [h_j_toNat]; exact h_j_lt_nat
      have h_4j_toNat : (4 * j).toNat = 4 * (w - 4 * k) := by
        rw [UInt32.toNat_mul, h_j_toNat]
        show (4 * (w - 4 * k)) % 2 ^ 32 = 4 * (w - 4 * k)
        omega
      have h_K_le_len := K_times_16_le_len s_entry
      have h_no_wrap_src : (getReg s_entry 14).toNat + (getReg s_entry 12).toNat ≤ 2 ^ 32 :=
        h_pre.2.2.2.2.2
      have h_no_wrap_dst : (getReg s_entry 13).toNat + (getReg s_entry 12).toNat ≤ 2 ^ 32 :=
        h_pre.2.2.2.2.1
      rw [loadWord_of_mem_eq h'_mem]
      have h_dst_addr : ((getReg s_entry 13).toNat + 4 * w : Nat).toUInt32
                      = getReg s 13 + 4 * j := by
        apply UInt32_eq_of_toNat_eq
        rw [UInt32.toNat_add, h_13, h_4j_toNat]
        show (BitVec.ofNat 32 _).toNat = _
        simp [BitVec.toNat_ofNat]; omega
      rw [h_dst_addr]
      rw [aligned16_body_loadWord_at_offset s (getReg s 13) (getReg s 14) j h_j_lt_uint]
      have h_src_addr : getReg s 14 + 4 * j
                      = ((getReg s_entry 14).toNat + 4 * w : Nat).toUInt32 := by
        apply UInt32_eq_of_toNat_eq
        rw [UInt32.toNat_add, h_14, h_4j_toNat]
        show _ = (BitVec.ofNat 32 _).toNat
        simp [BitVec.toNat_ofNat]; omega
      rw [h_src_addr]
      -- byte-by-byte src equality via h_mem_frame + Pre's non-aliasing.
      obtain ⟨h_a2_ge, _, _, h_no_alias, _, _⟩ := h_pre
      -- Helper: for b_off < 4, show (src+4w).toUInt32 + b_off = (src+4w+b_off.toNat).toUInt32.
      have h_bridge : ∀ (b_off : UInt32), b_off < 4 →
          ((getReg s_entry 14).toNat + 4 * w : Nat).toUInt32 + b_off
          = ((getReg s_entry 14).toNat + 4 * w + b_off.toNat : Nat).toUInt32 := by
        intro b_off hb_off
        apply UInt32_eq_of_toNat_eq
        rw [UInt32.toNat_add]
        show ((BitVec.ofNat 32 _).toNat + b_off.toNat) % 2 ^ 32 = (BitVec.ofNat 32 _).toNat
        simp [BitVec.toNat_ofNat]
      -- Helper: byte ≠ via Pre's non-aliasing.
      have h_byte_ne : ∀ (b_off : Nat), b_off < 4 →
          ∀ (w' : Nat), w' < 4 * k → ∀ (b' : Nat), b' < 4 →
          ((getReg s_entry 14).toNat + 4 * w + b_off : Nat).toUInt32
          ≠ ((getReg s_entry 13).toNat + 4 * w' + b' : Nat).toUInt32 := by
        intro b_off hb_off w' hw' b' hb' h_eq
        have h_4wb_toUInt32_toNat : ((4 * w + b_off : Nat).toUInt32).toNat = 4 * w + b_off := by
          show (BitVec.ofNat 32 _).toNat = _
          simp [BitVec.toNat_ofNat]
          omega
        have h_4w'b'_toUInt32_toNat : ((4 * w' + b' : Nat).toUInt32).toNat = 4 * w' + b' := by
          show (BitVec.ofNat 32 _).toNat = _
          simp [BitVec.toNat_ofNat]
          omega
        have h_lt_src : (4 * w + b_off : Nat).toUInt32 < getReg s_entry 12 := by
          apply UInt32.lt_iff_toNat_lt.mpr
          rw [h_4wb_toUInt32_toNat]; omega
        have h_lt_dst : (4 * w' + b' : Nat).toUInt32 < getReg s_entry 12 := by
          apply UInt32.lt_iff_toNat_lt.mpr
          rw [h_4w'b'_toUInt32_toNat]; omega
        have h_bridged : getReg s_entry 13 + (4 * w' + b' : Nat).toUInt32
                       = getReg s_entry 14 + (4 * w + b_off : Nat).toUInt32 := by
          apply UInt32_eq_of_toNat_eq
          rw [UInt32.toNat_add, UInt32.toNat_add, h_4wb_toUInt32_toNat, h_4w'b'_toUInt32_toNat]
          have := congrArg UInt32.toNat h_eq
          rw [show (((getReg s_entry 14).toNat + 4 * w + b_off : Nat).toUInt32).toNat
              = ((getReg s_entry 14).toNat + 4 * w + b_off) % 2 ^ 32 from by
                show (BitVec.ofNat 32 _).toNat = _; simp [BitVec.toNat_ofNat]] at this
          rw [show (((getReg s_entry 13).toNat + 4 * w' + b' : Nat).toUInt32).toNat
              = ((getReg s_entry 13).toNat + 4 * w' + b') % 2 ^ 32 from by
                show (BitVec.ofNat 32 _).toNat = _; simp [BitVec.toNat_ofNat]] at this
          omega
        exact h_no_alias _ _ h_lt_dst h_lt_src h_bridged
      apply loadWord_eq_of_bytes_eq
      · -- b = 0.
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 0 (by decide) w' hw' b' hb'
        simpa using this
      · -- b = 1.
        rw [h_bridge 1 (by decide)]
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 1 (by decide) w' hw' b' hb'
        show ((getReg s_entry 14).toNat + 4 * w + 1 : Nat).toUInt32 ≠ _
        exact this
      · -- b = 2.
        rw [h_bridge 2 (by decide)]
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 2 (by decide) w' hw' b' hb'
        show ((getReg s_entry 14).toNat + 4 * w + 2 : Nat).toUInt32 ≠ _
        exact this
      · -- b = 3.
        rw [h_bridge 3 (by decide)]
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 3 (by decide) w' hw' b' hb'
        show ((getReg s_entry 14).toNat + 4 * w + 3 : Nat).toUInt32 ≠ _
        exact this
  · -- Memory frame: addresses outside [dst + 16k, dst + 16(k+1)) are unchanged.
    intro a h_ne_all
    rw [h'_mem]
    rw [aligned16_body_mem_outside _ a.toUInt32 (getReg s 13) (getReg s 14) ?ho]
    · -- After peeling, goal: s.mem a.toUInt32 = s_entry.mem a.toUInt32.
      apply h_mem_frame a
      intro w hw b hb
      exact h_ne_all w (by omega) b hb
    case ho =>
      -- Need: ∀ i : UInt32, i < 16 → a.toUInt32 ≠ getReg s 13 + i.
      intro i hi
      have hi_nat : i.toNat < 16 := by
        have := UInt32.lt_iff_toNat_lt.mp hi; simpa using this
      -- Pick w = 4k + i.toNat/4, b = i.toNat % 4.
      have h_w : 4 * k + i.toNat / 4 < 4 * (k + 1) := by omega
      have h_b : i.toNat % 4 < 4 := by omega
      have h_arith :
          (getReg s_entry 13).toNat + 4 * (4 * k + i.toNat / 4) + i.toNat % 4
          = (getReg s_entry 13).toNat + 16 * k + i.toNat := by omega
      have h_ne := h_ne_all (4 * k + i.toNat / 4) h_w (i.toNat % 4) h_b
      rw [h_arith] at h_ne
      -- Bridge: getReg s 13 + i = (dst + 16k + i.toNat).toUInt32 (mod 2^32).
      have h_addr_eq :
          getReg s 13 + i = ((getReg s_entry 13).toNat + 16 * k + i.toNat).toUInt32 := by
        apply UInt32_eq_of_toNat_eq
        rw [getReg_13_plus_toNat s_entry s k i h_13]
        show _ = (Nat.toUInt32 _).toNat
        rfl
      rw [h_addr_eq]
      exact h_ne

theorem loop_inv_exit_aligned16 (s_entry : State)
    (h_K_pos : 0 < (aligned16_loop_count s_entry).toNat) :
    CFG mc
      (LoopInv_aligned16 s_entry ((aligned16_loop_count s_entry).toNat - 1))
      (fun _ s' => LoopPost_aligned16 s_entry s') := by
  intro s h_inv
  obtain ⟨h_pc, h_11, h_12, h_13, h_14, h_k_le, h_mem_copied, h_mem_frame, h_pre⟩ := h_inv
  obtain ⟨n, h_R⟩ := cfg_aligned16_body s h_pc
  refine ⟨n, ?_⟩
  simp only [R_aligned16_body] at h_R
  obtain ⟨h'_pc, h'_11, h'_12, h'_13, h'_14, h'_frame, h'_mem⟩ := h_R
  have h_K_le_len := K_times_16_le_len s_entry
  have h_tail_lt_16 := len_minus_K16_lt_16 s_entry
  -- Byte counter ≥ 16: we're about to consume the final chunk.
  have h_12_ge_16 : (getReg s 12).toNat ≥ 16 := by rw [h_12]; omega
  -- bltu NOT taken: at k = K-1, post-len < 16.
  have h_not_taken : (getReg s 11 < getReg s 12 + 0xFFFFFFF0) = false := by
    have h_not : ¬ (getReg s 11 < getReg s 12 + 0xFFFFFFF0) := fun h_lt => by
      have := UInt32.lt_iff_toNat_lt.mp h_lt
      rw [h_11, ptr_sub_16_toNat _ h_12_ge_16, h_12] at this
      have h_15 : (15 : UInt32).toNat = 15 := by decide
      omega
    simp [h_not]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h'_pc]; simp [h_not_taken, h_pc]
  · rw [h'_11]; exact h_11
  · rw [h'_12, ptr_sub_16_toNat _ h_12_ge_16, h_12]; omega
  · rw [h'_13, ptr_add_16_toNat, h_13]; omega
  · rw [h'_14, ptr_add_16_toNat, h_14]; omega
  · -- Memory copied.  ∀ w < 4*K, loadWord s' (dst + 4w).toUInt32 = loadWord s_entry (src + 4w).toUInt32.
    intro w hw
    by_cases h_case : w < 4 * ((aligned16_loop_count s_entry).toNat - 1)
    · -- Case 1: previously copied (w < 4*(K-1)).
      have h_k1_le : ((aligned16_loop_count s_entry).toNat - 1) + 1
                     ≤ (aligned16_loop_count s_entry).toNat := by omega
      apply Eq.trans _ (h_mem_copied w h_case)
      apply loadWord_eq_of_bytes_eq
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        have h := step_case1_byte_outside s_entry s _ h_pre h_13 h_k1_le w h_case 0 (by decide) i hi
        simpa using h
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        exact step_case1_byte_outside s_entry s _ h_pre h_13 h_k1_le w h_case 1 (by decide) i hi
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        exact step_case1_byte_outside s_entry s _ h_pre h_13 h_k1_le w h_case 2 (by decide) i hi
      · show (stepN mc n s).mem _ = s.mem _
        rw [h'_mem]
        apply aligned16_body_mem_outside
        intro i hi
        exact step_case1_byte_outside s_entry s _ h_pre h_13 h_k1_le w h_case 3 (by decide) i hi
    · -- Case 2: newly stored. w = 4*(K-1) + j_nat for j_nat ∈ {0..3}.
      have h_K := (aligned16_loop_count s_entry).toNat
      have h_K_pos' : 0 < (aligned16_loop_count s_entry).toNat := h_K_pos
      have h_w_ge : 4 * ((aligned16_loop_count s_entry).toNat - 1) ≤ w := by omega
      have h_j_lt_nat : w - 4 * ((aligned16_loop_count s_entry).toNat - 1) < 4 := by omega
      let j : UInt32 := (w - 4 * ((aligned16_loop_count s_entry).toNat - 1)).toUInt32
      have h_j_toNat : j.toNat = w - 4 * ((aligned16_loop_count s_entry).toNat - 1) := by
        show (BitVec.ofNat 32 _).toNat = _
        simp [BitVec.toNat_ofNat]; omega
      have h_j_lt_uint : j < 4 := by
        apply UInt32.lt_iff_toNat_lt.mpr
        rw [h_j_toNat]; exact h_j_lt_nat
      have h_4j_toNat : (4 * j).toNat
                      = 4 * (w - 4 * ((aligned16_loop_count s_entry).toNat - 1)) := by
        rw [UInt32.toNat_mul, h_j_toNat]
        show (4 * (w - 4 * ((aligned16_loop_count s_entry).toNat - 1))) % 2 ^ 32
             = 4 * (w - 4 * ((aligned16_loop_count s_entry).toNat - 1))
        omega
      have h_K_le_len := K_times_16_le_len s_entry
      have h_no_wrap_src : (getReg s_entry 14).toNat + (getReg s_entry 12).toNat ≤ 2 ^ 32 :=
        h_pre.2.2.2.2.2
      have h_no_wrap_dst : (getReg s_entry 13).toNat + (getReg s_entry 12).toNat ≤ 2 ^ 32 :=
        h_pre.2.2.2.2.1
      rw [loadWord_of_mem_eq h'_mem]
      have h_dst_addr : ((getReg s_entry 13).toNat + 4 * w : Nat).toUInt32
                      = getReg s 13 + 4 * j := by
        apply UInt32_eq_of_toNat_eq
        rw [UInt32.toNat_add, h_13, h_4j_toNat]
        show (BitVec.ofNat 32 _).toNat = _
        simp [BitVec.toNat_ofNat]; omega
      rw [h_dst_addr]
      rw [aligned16_body_loadWord_at_offset s (getReg s 13) (getReg s 14) j h_j_lt_uint]
      have h_src_addr : getReg s 14 + 4 * j
                      = ((getReg s_entry 14).toNat + 4 * w : Nat).toUInt32 := by
        apply UInt32_eq_of_toNat_eq
        rw [UInt32.toNat_add, h_14, h_4j_toNat]
        show _ = (BitVec.ofNat 32 _).toNat
        simp [BitVec.toNat_ofNat]; omega
      rw [h_src_addr]
      obtain ⟨h_a2_ge, _, _, h_no_alias, _, _⟩ := h_pre
      have h_bridge : ∀ (b_off : UInt32), b_off < 4 →
          ((getReg s_entry 14).toNat + 4 * w : Nat).toUInt32 + b_off
          = ((getReg s_entry 14).toNat + 4 * w + b_off.toNat : Nat).toUInt32 := by
        intro b_off _
        apply UInt32_eq_of_toNat_eq
        rw [UInt32.toNat_add]
        show ((BitVec.ofNat 32 _).toNat + b_off.toNat) % 2 ^ 32 = (BitVec.ofNat 32 _).toNat
        simp [BitVec.toNat_ofNat]
      have h_byte_ne : ∀ (b_off : Nat), b_off < 4 →
          ∀ (w' : Nat), w' < 4 * ((aligned16_loop_count s_entry).toNat - 1) →
            ∀ (b' : Nat), b' < 4 →
              ((getReg s_entry 14).toNat + 4 * w + b_off : Nat).toUInt32
              ≠ ((getReg s_entry 13).toNat + 4 * w' + b' : Nat).toUInt32 := by
        intro b_off hb_off w' hw' b' hb' h_eq
        have h_4wb_toUInt32_toNat :
            ((4 * w + b_off : Nat).toUInt32).toNat = 4 * w + b_off := by
          show (BitVec.ofNat 32 _).toNat = _
          simp [BitVec.toNat_ofNat]; omega
        have h_4w'b'_toUInt32_toNat :
            ((4 * w' + b' : Nat).toUInt32).toNat = 4 * w' + b' := by
          show (BitVec.ofNat 32 _).toNat = _
          simp [BitVec.toNat_ofNat]; omega
        have h_lt_src : (4 * w + b_off : Nat).toUInt32 < getReg s_entry 12 := by
          apply UInt32.lt_iff_toNat_lt.mpr
          rw [h_4wb_toUInt32_toNat]; omega
        have h_lt_dst : (4 * w' + b' : Nat).toUInt32 < getReg s_entry 12 := by
          apply UInt32.lt_iff_toNat_lt.mpr
          rw [h_4w'b'_toUInt32_toNat]; omega
        have h_bridged : getReg s_entry 13 + (4 * w' + b' : Nat).toUInt32
                       = getReg s_entry 14 + (4 * w + b_off : Nat).toUInt32 := by
          apply UInt32_eq_of_toNat_eq
          rw [UInt32.toNat_add, UInt32.toNat_add, h_4wb_toUInt32_toNat, h_4w'b'_toUInt32_toNat]
          have := congrArg UInt32.toNat h_eq
          rw [show (((getReg s_entry 14).toNat + 4 * w + b_off : Nat).toUInt32).toNat
              = ((getReg s_entry 14).toNat + 4 * w + b_off) % 2 ^ 32 from by
                show (BitVec.ofNat 32 _).toNat = _; simp [BitVec.toNat_ofNat]] at this
          rw [show (((getReg s_entry 13).toNat + 4 * w' + b' : Nat).toUInt32).toNat
              = ((getReg s_entry 13).toNat + 4 * w' + b') % 2 ^ 32 from by
                show (BitVec.ofNat 32 _).toNat = _; simp [BitVec.toNat_ofNat]] at this
          omega
        exact h_no_alias _ _ h_lt_dst h_lt_src h_bridged
      apply loadWord_eq_of_bytes_eq
      · apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 0 (by decide) w' hw' b' hb'
        simpa using this
      · rw [h_bridge 1 (by decide)]
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 1 (by decide) w' hw' b' hb'
        show ((getReg s_entry 14).toNat + 4 * w + 1 : Nat).toUInt32 ≠ _
        exact this
      · rw [h_bridge 2 (by decide)]
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 2 (by decide) w' hw' b' hb'
        show ((getReg s_entry 14).toNat + 4 * w + 2 : Nat).toUInt32 ≠ _
        exact this
      · rw [h_bridge 3 (by decide)]
        apply h_mem_frame
        intro w' hw' b' hb'
        have := h_byte_ne 3 (by decide) w' hw' b' hb'
        show ((getReg s_entry 14).toNat + 4 * w + 3 : Nat).toUInt32 ≠ _
        exact this
  · -- Memory frame.  Same shape as step's memory frame, with K-1 instead of k.
    intro a h_ne_all
    rw [h'_mem]
    rw [aligned16_body_mem_outside _ a.toUInt32 (getReg s 13) (getReg s 14) ?ho]
    · -- s.mem a.toUInt32 = s_entry.mem a.toUInt32 via h_mem_frame.
      apply h_mem_frame a
      intro w hw b hb
      exact h_ne_all w (by omega) b hb
    case ho =>
      intro i hi
      have hi_nat : i.toNat < 16 := by
        have := UInt32.lt_iff_toNat_lt.mp hi; simpa using this
      have h_w : 4 * ((aligned16_loop_count s_entry).toNat - 1) + i.toNat / 4
                 < 4 * (aligned16_loop_count s_entry).toNat := by omega
      have h_b : i.toNat % 4 < 4 := by omega
      have h_arith :
          (getReg s_entry 13).toNat
            + 4 * (4 * ((aligned16_loop_count s_entry).toNat - 1) + i.toNat / 4)
            + i.toNat % 4
          = (getReg s_entry 13).toNat
            + 16 * ((aligned16_loop_count s_entry).toNat - 1) + i.toNat := by omega
      have h_ne := h_ne_all (4 * ((aligned16_loop_count s_entry).toNat - 1) + i.toNat / 4)
                              h_w (i.toNat % 4) h_b
      rw [h_arith] at h_ne
      have h_addr_eq :
          getReg s 13 + i = ((getReg s_entry 13).toNat
                              + 16 * ((aligned16_loop_count s_entry).toNat - 1)
                              + i.toNat).toUInt32 := by
        apply UInt32_eq_of_toNat_eq
        rw [getReg_13_plus_toNat s_entry s _ i h_13]
        show _ = (Nat.toUInt32 _).toNat
        rfl
      rw [h_addr_eq]
      exact h_ne
  · -- getReg s' 12 < 16.
    have h_s'12_nat : (getReg (stepN mc n s) 12).toNat < 16 := by
      rw [h'_12, ptr_sub_16_toNat _ h_12_ge_16, h_12]; omega
    exact UInt32.lt_iff_toNat_lt.mpr h_s'12_nat

theorem K_pos_of_pre_aligned16 (s : State) (h : s.pc = 0x200a18 ∧ Pre_aligned16_loop s) :
    0 < (aligned16_loop_count s).toNat := by
  have h_a2_ge_16 : 16 ≤ getReg s 12 := h.2.1
  have h_K_pos : (0 : UInt32) < aligned16_loop_count s := by
    unfold aligned16_loop_count
    revert h_a2_ge_16
    generalize getReg s 12 = a2
    intro; bv_decide
  exact UInt32.lt_iff_toNat_lt.mp h_K_pos

/-! ## 6. Main theorem: full aligned 16-byte loop semantics, via `CFG.do_while`. -/

theorem aligned16_loop_correct :
    CFG mc
      (fun s => s.pc = 0x200a18 ∧ Pre_aligned16_loop s)
      LoopPost_aligned16 :=
  CFG.do_while
    (K := fun s => (aligned16_loop_count s).toNat)
    (Inv := LoopInv_aligned16)
    loop_inv_init_aligned16
    loop_inv_step_aligned16
    loop_inv_exit_aligned16
    K_pos_of_pre_aligned16

end MemcpyProof.Hoare
