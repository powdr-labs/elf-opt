/-
A small basic block from memcpy with full Hoare-triple semantics,
derived compositionally from per-instruction triples.

Everything is stated as `Triple block R` — no `runInstrs` in any
user-facing lemma's statement.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## The 4-byte tail-copy block (memcpy PCs 0x200a74..0x200a80).

  lw   a1, 0(a4)    -- a1 ← Mem[a4]      (a1 = x11, a4 = x14)
  sw   a1, 0(a3)    -- Mem[a3] ← a1      (a3 = x13)
  addi a3, a3, 4    -- a3 += 4
  addi a4, a4, 4    -- a4 += 4

Presented as a `List Instr` — no PC, no `code`, no memory layout. -/

def block_4byte : List Instr :=
  [ Instr.lw   11 14 0
  , Instr.sw   13 11 0
  , Instr.addi 13 13 4
  , Instr.addi 14 14 4
  ]

theorem block_4byte_triple_composed :
    Triple block_4byte
      (RComp (fun s s' => s' = advance (setReg s 11 (loadWord s (getReg s 14 + 0))))
        (RComp (fun s s' => s' = advance (storeWord s (getReg s 13 + 0) (getReg s 11)))
          (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 13 + 4)))
                 (fun s s' => s' = advance (setReg s 14 (getReg s 14 + 4)))))) :=
  (Triple_lw   11 14 0).append <|
  (Triple_sw   13 11 0).append <|
  (Triple_addi 13 13 4).append <|
  (Triple_addi 14 14 4)

/-- Clean relational post-condition for `block_4byte`. -/
def R_block_4byte : State → State → Prop :=
  fun s s' =>
    let loaded : UInt32 := loadWord s (getReg s 14)
    s'.pc = s.pc + 16 ∧
    getReg s' 11 = loaded ∧
    getReg s' 13 = getReg s 13 + 4 ∧
    getReg s' 14 = getReg s 14 + 4 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 13 → r.val ≠ 14 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeWord s (getReg s 13) loaded).mem

theorem block_4byte_triple : Triple block_4byte R_block_4byte := by
  refine Triple.weaken block_4byte_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 = s.pc + 16 := by bv_decide
  simp [R_block_4byte, h_pc]
  refine ⟨?_, ?_⟩
  · intro r hr11 hr13 hr14
    simp [setReg, Ne.symm hr11, Ne.symm hr13, Ne.symm hr14]
  · unfold storeWord; simp [storeByte]

/-- Byte-level view of `block_4byte`'s memory effect: the 4 stored bytes
    equal the 4 src bytes.  Derivable from `R_block_4byte`'s single
    `storeWord` via `storeWord_mem_byte` + `unfold loadWord`. -/
theorem block_4byte_mem_bytes (s : State) (i : UInt32) (hi : i < 4) :
    (runInstrs s block_4byte).mem (getReg s 13 + i) = s.mem (getReg s 14 + i) := by
  sorry

end MemcpyProof.Hoare
