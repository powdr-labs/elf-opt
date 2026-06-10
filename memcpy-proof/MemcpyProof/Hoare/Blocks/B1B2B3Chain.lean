/-
End-to-end CFG composition: B1 → B2 → B3.

This file demonstrates the `CFG` framework's compositional structure
by chaining three already-proved fragments:

  * B1 (`block_align_check`, PCs 0x002008f8..0x00200908):
      computes the dispatch predicate, branches on it.
  * B2 (the byte-prefix loop, PCs 0x0020090c..0x00200944):
      `byte_prefix_loop_correct` from `LoopBytePrefixCFG`.
  * B3 (`block_B3`, PC 0x00200948):
      `andi a1, a3, 3` — single-instr setup for the alignment dispatch.

The chain runs from entry-at-B1, through B1's fall-through (i.e., src
misaligned ∧ n ≠ 0), through the loop, and across B3 to PC 0x0020094c.
The composed post-relation captures the K bytes copied and the final
register / memory state.
-/

import MemcpyProof.Hoare.BlockPrefix
import MemcpyProof.Hoare.Blocks.Simple
import MemcpyProof.Hoare.Blocks.LoopBytePrefixCFG
import MemcpyProof.Extract

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## 1. `CodeMatchesBlock` lemmas for B1 and B3. -/

theorem mc_matches_block_align_check (s : State) (h : s.pc = 0x002008f8) :
    CodeMatchesBlock mc s block_align_check := by mc_matches

theorem mc_matches_block_B3 (s : State) (h : s.pc = 0x00200948) :
    CodeMatchesBlock mc s block_B3 := by mc_matches

/-! ## 2. Per-block CFG fragments via `CFG_of_Triple_at`. -/

theorem cfg_block_align_check :
    CFG mc (fun s => s.pc = 0x002008f8) R_block_align_check :=
  CFG_of_Triple_at 0x002008f8 block_align_check_triple
    (fun s h => mc_matches_block_align_check s h)

theorem cfg_block_B3 :
    CFG mc (fun s => s.pc = 0x00200948)
      (fun s s' => s' = advance (setReg s 11 (getReg s 13 &&& 3))) :=
  CFG_of_Triple_at 0x00200948 block_B3_triple
    (fun s h => mc_matches_block_B3 s h)

/-! ## 3. The chain entry condition.

`B1`'s bne falls through (into B2) exactly when `(src & 3) ≠ 0 ∧ n ≠ 0`.
The rest of `Pre_loop_byte_prefix` (non-aliasing, no pointer wrap) is
inherited from the entry. -/

def Pre_b1_entry (s : State) : Prop :=
  s.pc = 0x002008f8 ∧
  (getReg s 11 &&& 3) ≠ 0 ∧
  getReg s 12 ≠ 0 ∧
  (∀ i j : UInt32, i < getReg s 12 → j < getReg s 12 →
    getReg s 10 + i ≠ getReg s 11 + j) ∧
  (getReg s 10).toNat + (getReg s 12).toNat ≤ 2 ^ 32 ∧
  (getReg s 11).toNat + (getReg s 12).toNat ≤ 2 ^ 32

/-! ## 4. The chained post-relation. -/

/-- Post-relation of the B1 → B2 → B3 chain.

  After B1's fall-through, B2's `K` byte-loop iterations, and B3's
  one-instruction `andi`, we arrive at PC `0x0020094c` with `K` bytes
  copied.  Since B1 doesn't touch a0/a1/a2 and B3 doesn't touch
  a0/a2/mem, the relation can be stated directly in terms of the
  original `s`. -/
def R_b1_b2_b3 (s s' : State) : Prop :=
  let K := loop_byte_prefix_count s
  let a0 := getReg s 10
  let a1 := getReg s 11
  let a2 := getReg s 12
  s'.pc = 0x0020094c ∧
  getReg s' 10 = a0 ∧
  getReg s' 12 = a2 - K ∧
  (∀ i : UInt32, i < K → s'.mem (a0 + i) = s.mem (a1 + i)) ∧
  (∀ a : UInt32, (∀ i : UInt32, i < K → a ≠ a0 + i) → s'.mem a = s.mem a)

/-! ## 5. The chained theorem.

Composed via the new `CFG.trans_with_pre` + `CFG.weaken_with_pre`
combinators.  The mid-functions can use the entry precondition, which
is what makes B1's fall-through case provable (it depends on
`Pre_b1_entry`'s `(a1 & 3) ≠ 0 ∧ a2 ≠ 0`). -/

/-- Frame-on-non-modified-regs helper for B1: a0/a1/a2 are preserved. -/
private theorem b1_frame_a012 (s s' : State) (hR : R_block_align_check s s') :
    getReg s' 10 = getReg s 10 ∧
    getReg s' 11 = getReg s 11 ∧
    getReg s' 12 = getReg s 12 := by
  obtain ⟨_, _, _, h1_frame, _⟩ := hR
  refine ⟨?_, ?_, ?_⟩ <;>
    (show s'.regs[_] = s.regs[_]; exact h1_frame ⟨_, by decide⟩ (by decide) (by decide))

theorem cfg_b1_b2_b3 :
    CFG mc Pre_b1_entry R_b1_b2_b3 := by
  -- B1 lifted to start from `Pre_b1_entry`.
  have h_b1 : CFG mc Pre_b1_entry R_block_align_check :=
    CFG.strengthen (fun _ hP => hP.1) cfg_block_align_check
  -- B1 → B2: under entry's premises, B1's post lands us at B2's pre.
  have h_mid_12 : ∀ s s', Pre_b1_entry s → R_block_align_check s s' →
      (s'.pc = 0x0020090c ∧ Pre_loop_byte_prefix s') := by
    rintro s s' ⟨h_pc, h_align, h_a2_ne, h_no_alias, h_no_wrap_a0, h_no_wrap_a1⟩ hR
    obtain ⟨h_10, h_11, h_12⟩ := b1_frame_a012 s s' hR
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1_pc, _⟩ := hR
      have h_v13_false : ((getReg s 11 &&& 3) == 0) = false := by simp; exact h_align
      have h_v14_false : (getReg s 12 == 0) = false := by simp; exact h_a2_ne
      rw [h1_pc, h_v13_false, h_v14_false]; simp; rw [h_pc]; decide
    · rw [h_11]; exact h_align
    · rw [h_12]; exact h_a2_ne
    · rw [h_10, h_11, h_12]; exact h_no_alias
    · rw [h_10, h_12]; exact h_no_wrap_a0
    · rw [h_11, h_12]; exact h_no_wrap_a1
  have h_b1_b2 := CFG.trans_with_pre h_b1 h_mid_12 byte_prefix_loop_correct
  -- B1+B2 → B3: B2's LoopPost gives pc = 0x00200948.
  have h_mid_23 : ∀ s s', RComp R_block_align_check LoopPost s s' →
      s'.pc = 0x00200948 := by
    rintro s s' ⟨_, _, hLoop⟩; exact hLoop.1
  have h_b1_b2_b3 := CFG.trans h_b1_b2 h_mid_23 cfg_block_B3
  -- Weaken the composed RComp into the cleaner `R_b1_b2_b3`.
  apply CFG.weaken_with_pre h_b1_b2_b3
  intro s s_final hP hChain
  -- RComp (RComp R_b1 LoopPost) R_B3 = ∃ s2, (∃ s1, R_b1 s s1 ∧ LoopPost s1 s2) ∧ R_B3 s2 s_final
  obtain ⟨s2, ⟨s1, hR1, hLoop⟩, hB3⟩ := hChain
  obtain ⟨_, h_align, h_a2_ne, _⟩ := hP
  simp only [LoopPost] at hLoop
  obtain ⟨h2_pc, h2_10, _, h2_12, _, _, h2_mem_copied, h2_mem_frame, _⟩ := hLoop
  obtain ⟨h_10, h_11, h_12⟩ := b1_frame_a012 s s1 hR1
  have h1_mem : s1.mem = s.mem := hR1.2.2.2.2
  have h_K_eq : loop_byte_prefix_count s1 = loop_byte_prefix_count s := by
    unfold loop_byte_prefix_count; rw [h_11, h_12]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hB3]; simp [h2_pc]
  · rw [hB3]; simp; rw [h2_10, h_10]
  · rw [hB3]; simp; rw [h2_12, h_12, h_K_eq]
  · intro i hi
    rw [hB3]; show (advance _).mem _ = _; rw [advance_mem, setReg_mem]
    have := h2_mem_copied i (h_K_eq ▸ hi)
    rw [h_10, h_11] at this
    rw [this, h1_mem]
  · intro a h_ne
    rw [hB3]; show (advance _).mem _ = _; rw [advance_mem, setReg_mem]
    have h_ne' : ∀ i, i < loop_byte_prefix_count s1 → a ≠ getReg s1 10 + i := by
      intro i hi; rw [h_10]; exact h_ne i (h_K_eq ▸ hi)
    rw [h2_mem_frame a h_ne', h1_mem]

end MemcpyProof.Hoare
