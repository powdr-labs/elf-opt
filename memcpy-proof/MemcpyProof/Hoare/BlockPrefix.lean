/-
The memcpy prefix block (PCs 0x002008f8..0x00200904).

Four instructions that compute, in `a3`, the predicate
"src is word-aligned, OR n is zero" — this is what the subsequent
`bne a3, zero, +0xf8` at PC 0x00200908 dispatches on.

  andi  a3, a1, 3      -- a3 ← a1 & 3            (= src low 2 bits)
  sltiu a3, a3, 1      -- a3 ← (a3 < 1) ? 1 : 0  (= "src aligned")
  sltiu a4, a2, 1      -- a4 ← (a2 < 1) ? 1 : 0  (= "n is 0")
  or    a3, a3, a4     -- a3 ← src_aligned ∨ (n = 0)
-/

import MemcpyProof.Hoare.InstrTriples
import MemcpyProof.Hoare.StateLemmas
import Std.Tactic.BVDecide

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

def block_align_check : List Instr :=
  [ Instr.andi  13 11 3
  , Instr.sltiu 13 13 1
  , Instr.sltiu 14 12 1
  , Instr.or_   13 13 14
  ]

theorem block_align_check_triple_composed :
    Triple block_align_check
      (RComp (fun s s' => s' = advance (setReg s 13 (getReg s 11 &&& 3)))
        (RComp (fun s s' => s' = advance (setReg s 13 (if getReg s 13 < 1 then 1 else 0)))
          (RComp (fun s s' => s' = advance (setReg s 14 (if getReg s 12 < 1 then 1 else 0)))
                 (fun s s' => s' = advance (setReg s 13 (getReg s 13 ||| getReg s 14)))))) :=
  (Triple_andi  13 11 3).append <|
  (Triple_sltiu 13 13 1).append <|
  (Triple_sltiu 14 12 1).append <|
  (Triple_or    13 13 14)

def R_block_align_check : State → State → Prop :=
  fun s s' =>
    let v13 : Bool := (getReg s 11 &&& 3) == 0
    let v14 : Bool := getReg s 12 == 0
    s'.pc = s.pc + 16 ∧
    getReg s' 13 = (v13 || v14).toUInt32 ∧
    getReg s' 14 = v14.toUInt32 ∧
    (∀ r : Fin 32, r.val ≠ 13 → r.val ≠ 14 → s'.regs[r.val] = s.regs[r.val]) ∧
    s'.mem = s.mem

theorem block_align_check_triple : Triple block_align_check R_block_align_check := by
  refine Triple.weaken block_align_check_triple_composed ?_
  rintro s s' ⟨_, rfl, _, rfl, _, rfl, rfl⟩
  grind [Bool.toUInt32, R_block_align_check]

end MemcpyProof.Hoare
