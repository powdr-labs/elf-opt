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

/-- A useful single-instruction triple: when not halted, the post-state
    is `exec s i`.  (When halted, `runInstrs` returns `s` unchanged, so
    a "the post-state is `exec s i`" claim is only sensible under the
    not-halted hypothesis — hence the implication in the relation.) -/
theorem Triple_single_not_halted (i : Instr) :
    Triple [i] (fun s s' => s.halted = false → s' = exec s i) := by
  intro s h_halted
  show (if s.halted then s else runInstrs (exec s i) []) = exec s i
  rw [h_halted]; rfl

/-- Sequential composition (the textbook `seq` rule for relational Hoare).
    `Triple b₁ R₁` and `Triple b₂ R₂` compose into `Triple (b₁ ++ b₂) (R₁;R₂)`. -/
theorem Triple.append {b₁ b₂ : List Instr} {R₁ R₂ : State → State → Prop}
    (h₁ : Triple b₁ R₁) (h₂ : Triple b₂ R₂) :
    Triple (b₁ ++ b₂) (RComp R₁ R₂) := by
  intro s
  refine ⟨runInstrs s b₁, h₁ s, ?_⟩
  show R₂ (runInstrs s b₁) (runInstrs s (b₁ ++ b₂))
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
