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
    CodeMatchesBlock mc s block_align_check := by
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · show decode (mc s.pc) = Instr.andi 13 11 3
    rw [h]; rfl
  · rw [show (exec s (Instr.andi 13 11 3)).pc = 0x002008fc from by simp [h]]; rfl
  · rw [show (exec (exec s _) (Instr.sltiu 13 13 1)).pc = 0x00200900 from by simp [h]]; rfl
  · rw [show (exec (exec (exec s _) _) (Instr.sltiu 14 12 1)).pc = 0x00200904 from by simp [h]]
    rfl
  · rw [show (exec (exec (exec (exec s _) _) _) (Instr.or_ 13 13 14)).pc = 0x00200908
          from by simp [h]]
    rfl

theorem mc_matches_block_B3 (s : State) (h : s.pc = 0x00200948) :
    CodeMatchesBlock mc s block_B3 := by
  refine ⟨?_, trivial⟩
  show decode (mc s.pc) = Instr.andi 11 13 3
  rw [h]; rfl

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

Manual stepN chaining (rather than `CFG.trans`) because B1's post
doesn't carry the entry-precondition info, so the "mid" function would
need access to `Pre_b1_entry`'s premises (which `CFG.trans`'s signature
doesn't expose).  We just unfold and chain `cfg_block_align_check`,
`byte_prefix_loop_correct`, and `cfg_block_B3`. -/

theorem cfg_b1_b2_b3 :
    CFG mc Pre_b1_entry R_b1_b2_b3 := by
  intro s hP
  obtain ⟨h_pc, h_align, h_a2_ne, h_no_alias, h_no_wrap_a0, h_no_wrap_a1⟩ := hP
  -- B1.
  obtain ⟨n1, hR1⟩ := cfg_block_align_check s h_pc
  simp only [R_block_align_check] at hR1
  obtain ⟨h1_pc, h1_13, h1_14, h1_frame, h1_mem⟩ := hR1
  have h_v13_false : ((getReg s 11 &&& 3) == 0) = false := by simp; exact h_align
  have h_v14_false : (getReg s 12 == 0) = false := by simp; exact h_a2_ne
  have h_s1_pc : (stepN mc n1 s).pc = 0x0020090c := by
    rw [h1_pc, h_v13_false, h_v14_false]; simp; rw [h_pc]; decide
  have h_s1_10 : getReg (stepN mc n1 s) 10 = getReg s 10 := by
    show (stepN mc n1 s).regs[10] = s.regs[10]
    exact h1_frame ⟨10, by decide⟩ (by decide) (by decide)
  have h_s1_11 : getReg (stepN mc n1 s) 11 = getReg s 11 := by
    show (stepN mc n1 s).regs[11] = s.regs[11]
    exact h1_frame ⟨11, by decide⟩ (by decide) (by decide)
  have h_s1_12 : getReg (stepN mc n1 s) 12 = getReg s 12 := by
    show (stepN mc n1 s).regs[12] = s.regs[12]
    exact h1_frame ⟨12, by decide⟩ (by decide) (by decide)
  have h_pre_loop : Pre_loop_byte_prefix (stepN mc n1 s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_s1_11]; exact h_align
    · rw [h_s1_12]; exact h_a2_ne
    · rw [h_s1_10, h_s1_11, h_s1_12]; exact h_no_alias
    · rw [h_s1_10, h_s1_12]; exact h_no_wrap_a0
    · rw [h_s1_11, h_s1_12]; exact h_no_wrap_a1
  -- B2.
  obtain ⟨n2, hR2⟩ := byte_prefix_loop_correct (stepN mc n1 s) ⟨h_s1_pc, h_pre_loop⟩
  simp only [LoopPost] at hR2
  obtain ⟨h2_pc, h2_10, _, h2_12, _, _, h2_mem_copied, h2_mem_frame, _⟩ := hR2
  -- B3.
  obtain ⟨n3, hR3⟩ := cfg_block_B3 (stepN mc n2 (stepN mc n1 s)) h2_pc
  refine ⟨n1 + n2 + n3, ?_⟩
  -- Combine via stepN_add.
  rw [stepN_add, stepN_add]
  -- s3 := stepN mc n3 (stepN mc n2 (stepN mc n1 s)) = advance (setReg ... 11 ...)
  have h_K_eq : loop_byte_prefix_count (stepN mc n1 s) = loop_byte_prefix_count s := by
    unfold loop_byte_prefix_count; rw [h_s1_11, h_s1_12]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- pc = 0x0020094c
    rw [hR3]; simp [h2_pc]
  · -- getReg s3 10 = getReg s 10
    rw [hR3]; simp; rw [h2_10, h_s1_10]
  · -- getReg s3 12 = getReg s 12 - K
    rw [hR3]; simp; rw [h2_12, h_s1_12, h_K_eq]
  · -- ∀ i < K, mem(a0 + i) = src.mem(a1 + i)
    intro i hi
    rw [hR3]
    show (advance _).mem (getReg s 10 + i) = s.mem (getReg s 11 + i)
    rw [advance_mem, setReg_mem]
    have hi' : i < loop_byte_prefix_count (stepN mc n1 s) := by rw [h_K_eq]; exact hi
    have := h2_mem_copied i hi'
    rw [h_s1_10, h_s1_11] at this
    rw [this, h1_mem]
  · -- ∀ a, (∀ i < K, a ≠ a0 + i) → s3.mem a = s.mem a
    intro a h_ne
    rw [hR3]
    show (advance _).mem a = s.mem a
    rw [advance_mem, setReg_mem]
    have h_ne' : ∀ i : UInt32, i < loop_byte_prefix_count (stepN mc n1 s) →
                  a ≠ getReg (stepN mc n1 s) 10 + i := by
      intro i hi
      rw [h_s1_10]
      exact h_ne i (h_K_eq ▸ hi)
    have := h2_mem_frame a h_ne'
    rw [this, h1_mem]

end MemcpyProof.Hoare
