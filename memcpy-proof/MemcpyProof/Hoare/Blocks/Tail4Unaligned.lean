/-
B28 — `4byte_unaligned` tail (11 instr, PCs 0x200ba8..0x200bd0).

Byte-by-byte copy of 4 bytes when the dst buffer is misaligned.

  lb   a1, 0(a4)         -- a1 ← signExt Mem[a4]
  lb   a5, 1(a4)
  lb   a6, 2(a4)
  sb   a1, 0(a3)         -- Mem[a3]   ← (a1 as UInt8)
  sb   a5, 1(a3)
  lb   a1, 3(a4)         -- a1 ← signExt Mem[a4+3]  (overwrites!)
  sb   a6, 2(a3)
  addi a4, a4, 4
  addi a5, a3, 4
  sb   a1, 3(a3)
  addi a3, a5, 0         -- a3 ← a5  (= old a3 + 4)

Split into 5 + 6 to keep RComp depth manageable.
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Half 1 (5 instr): 3 lb + 2 sb. -/

private def block_4byte_unaligned_h1 : List Instr :=
  [ Instr.lb 11 14 0
  , Instr.lb 15 14 1
  , Instr.lb 16 14 2
  , Instr.sb 13 11 0
  , Instr.sb 13 15 1
  ]

private theorem block_4byte_unaligned_h1_triple_composed :
    Triple block_4byte_unaligned_h1
      (RComp (fun s s' => s' = advance (setReg s 11 (signExt (loadByte s (getReg s 14 + 0)).toUInt32 7)))
        (RComp (fun s s' => s' = advance (setReg s 15 (signExt (loadByte s (getReg s 14 + 1)).toUInt32 7)))
          (RComp (fun s s' => s' = advance (setReg s 16 (signExt (loadByte s (getReg s 14 + 2)).toUInt32 7)))
            (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 0) (getReg s 11).toUInt8))
                  (fun s s' => s' = advance (storeByte s (getReg s 13 + 1) (getReg s 15).toUInt8))))))  :=
  (Triple_lb 11 14 0).append <|
  (Triple_lb 15 14 1).append <|
  (Triple_lb 16 14 2).append <|
  (Triple_sb 13 11 0).append <|
  (Triple_sb 13 15 1)

private def R_4u_h1 : State → State → Prop :=
  fun s s' =>
    let a3 := getReg s 13
    let a4 := getReg s 14
    let b0 : UInt32 := signExt (loadByte s a4).toUInt32 7
    let b1 : UInt32 := signExt (loadByte s (a4 + 1)).toUInt32 7
    let b2 : UInt32 := signExt (loadByte s (a4 + 2)).toUInt32 7
    s'.pc = s.pc + 20 ∧
    getReg s' 11 = b0 ∧
    getReg s' 13 = a3 ∧
    getReg s' 14 = a4 ∧
    getReg s' 15 = b1 ∧
    getReg s' 16 = b2 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 15 → r.val ≠ 16 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte (storeByte s a3 b0.toUInt8) (a3 + 1) b1.toUInt8).mem

private theorem block_4byte_unaligned_h1_triple :
    Triple block_4byte_unaligned_h1 R_4u_h1 := by
  refine Triple.weaken block_4byte_unaligned_h1_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 = s.pc + 20 := by bv_decide
  simp [R_4u_h1, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h11 h15 h16
    simp [setReg, Ne.symm h11, Ne.symm h15, Ne.symm h16]
  · unfold storeByte; simp

/-! ## Half 2 (6 instr): 1 lb, 1 sb, 1 addi, 1 addi, 1 sb, 1 addi. -/

private def block_4byte_unaligned_h2 : List Instr :=
  [ Instr.lb   11 14 3
  , Instr.sb   13 16 2
  , Instr.addi 14 14 4
  , Instr.addi 15 13 4
  , Instr.sb   13 11 3
  , Instr.addi 13 15 0
  ]

private theorem block_4byte_unaligned_h2_triple_composed :
    Triple block_4byte_unaligned_h2
      (RComp (fun s s' => s' = advance (setReg s 11 (signExt (loadByte s (getReg s 14 + 3)).toUInt32 7)))
        (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 2) (getReg s 16).toUInt8))
          (RComp (fun s s' => s' = advance (setReg s 14 (getReg s 14 + 4)))
            (RComp (fun s s' => s' = advance (setReg s 15 (getReg s 13 + 4)))
              (RComp (fun s s' => s' = advance (storeByte s (getReg s 13 + 3) (getReg s 11).toUInt8))
                    (fun s s' => s' = advance (setReg s 13 (getReg s 15 + 0)))))))) :=
  (Triple_lb   11 14 3).append <|
  (Triple_sb   13 16 2).append <|
  (Triple_addi 14 14 4).append <|
  (Triple_addi 15 13 4).append <|
  (Triple_sb   13 11 3).append <|
  (Triple_addi 13 15 0)

private def R_4u_h2 : State → State → Prop :=
  fun s s' =>
    let a3 := getReg s 13
    let a4 := getReg s 14
    let b3 : UInt32 := signExt (loadByte s (a4 + 3)).toUInt32 7
    s'.pc = s.pc + 24 ∧
    getReg s' 11 = b3 ∧
    getReg s' 13 = a3 + 4 ∧
    getReg s' 14 = a4 + 4 ∧
    getReg s' 15 = a3 + 4 ∧
    getReg s' 16 = getReg s 16 ∧
    (∀ r : Fin 32, r.val ≠ 11 → r.val ≠ 13 → r.val ≠ 14 → r.val ≠ 15 →
       s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = (storeByte (storeByte s (a3 + 2) (getReg s 16).toUInt8)
                        (a3 + 3) b3.toUInt8).mem

private theorem block_4byte_unaligned_h2_triple :
    Triple block_4byte_unaligned_h2 R_4u_h2 := by
  refine Triple.weaken block_4byte_unaligned_h2_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have h_pc : s.pc + 4 + 4 + 4 + 4 + 4 + 4 = s.pc + 24 := by bv_decide
  simp [R_4u_h2, h_pc]
  refine ⟨?_, ?_⟩
  · intro r h11 h13 h14 h15
    simp [setReg, Ne.symm h11, Ne.symm h13, Ne.symm h14, Ne.symm h15]
  · unfold storeByte; simp

/-! ## B28 — assembled. -/

def block_4byte_unaligned : List Instr :=
  block_4byte_unaligned_h1 ++ block_4byte_unaligned_h2

theorem block_4byte_unaligned_triple_composed :
    Triple block_4byte_unaligned (RComp R_4u_h1 R_4u_h2) :=
  block_4byte_unaligned_h1_triple.append block_4byte_unaligned_h2_triple

end MemcpyProof.Hoare
