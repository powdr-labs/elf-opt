/-
Relational Hoare triples for basic blocks (lists of instructions).

A `Triple block R` says: for every initial state `s`, the relation `R`
holds between `s` and `runInstrs s block`.  Because `runInstrs` is
total and deterministic, this is the strongest possible Hoare statement
about the block — it carries no less information than the equational
`runInstrs s block = f s` form.

Composition is by *list append* on the program side and *relational
composition* (`RComp`) on the property side.  That's the textbook
sequential composition rule, specialised to `runInstrs` and `++`.
-/

import MemcpyProof.Hoare.Block

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-- Relational Hoare triple: for every `s`, the binary relation `R`
    holds between `s` and the post-state `runInstrs s block`.  -/
def Triple (block : List Instr) (R : State → State → Prop) : Prop :=
  ∀ s, R s (runInstrs s block)

/-- Relational composition.  `(RComp R₁ R₂) s s'` means there exists an
    intermediate state `m` with `R₁ s m` and `R₂ m s'`. -/
def RComp (R₁ R₂ : State → State → Prop) : State → State → Prop :=
  fun s s' => ∃ m, R₁ s m ∧ R₂ m s'

@[simp] theorem RComp_def (R₁ R₂ : State → State → Prop) (s s' : State) :
    RComp R₁ R₂ s s' ↔ ∃ m, R₁ s m ∧ R₂ m s' := Iff.rfl

/-- Trivial triple: empty block leaves the state unchanged. -/
theorem Triple_nil (R : State → State → Prop) (h : ∀ s, R s s) : Triple [] R := by
  intro s; exact h s

/-- The fundamental single-instruction triple: the post-state is `exec s i`. -/
theorem Triple_single (i : Instr) :
    Triple [i] (fun s s' => s' = exec s i) := by
  intro s; rfl

/-- Sequential composition (the textbook `seq` rule for relational Hoare). -/
theorem Triple.append {b₁ b₂ : List Instr} {R₁ R₂ : State → State → Prop}
    (h₁ : Triple b₁ R₁) (h₂ : Triple b₂ R₂) :
    Triple (b₁ ++ b₂) (RComp R₁ R₂) := by
  intro s
  refine ⟨runInstrs s b₁, h₁ s, ?_⟩
  rw [runInstrs_append]
  exact h₂ (runInstrs s b₁)

/-- Postcondition weakening: if `R s s'` implies `R' s s'`, then a triple
    in `R` implies a triple in `R'`. -/
theorem Triple.weaken {block : List Instr} {R R' : State → State → Prop}
    (h : Triple block R) (imp : ∀ s s', R s s' → R' s s') : Triple block R' :=
  fun s => imp s _ (h s)

/-- Strongest postcondition: the relation `s' = runInstrs s block` is
    a Triple, and any other Triple is implied by this one. -/
theorem Triple_sp (block : List Instr) :
    Triple block (fun s s' => s' = runInstrs s block) := by
  intro s; rfl

end MemcpyProof.Hoare
