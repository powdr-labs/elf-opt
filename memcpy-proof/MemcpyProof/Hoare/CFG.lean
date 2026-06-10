/-
CFG-level Hoare reasoning over a `code : UInt32 → UInt32` map.

The existing `Triple block R` captures the semantics of a single
straight-line basic block: running the explicit list `block` from any
entry state `s` yields the post-state `runInstrs s block`, with
`R s s'`.  `runInstrs` doesn't consult the program counter — it just
folds `exec` over a fixed list of instructions.  That's fine for
sequential composition (via `Triple.append`), but it can't model
back-edges or any other dynamic control flow.

Here we lift `Triple` to a control-flow graph: execution is
`step code s := exec s (decode (code s.pc))`, which DOES consult the pc.
Many steps yield `stepN code n s`, and a CFG-level "Hoare triple"

  `CFG code P R := ∀ s, P s → ∃ n, R s (stepN code n s)`

says: from any state satisfying `P`, some finite number of steps yields
a state related to the entry by `R`.

The key bridge `CFG_of_Triple` turns any existing per-block `Triple` into
a CFG fragment, provided `code` matches the block at the visited pcs.
Loops are handled in a follow-on file via a CFG-level Hoare while-rule.
-/

import MemcpyProof.Hoare.Triple

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-! ## Step relation. -/

/-- One step of execution: fetch + decode + execute. -/
@[reducible] def step (code : UInt32 → UInt32) (s : State) : State :=
  exec s (decode (code s.pc))

/-- Iterated `step`: take `n` steps from `s` under `code`. -/
def stepN (code : UInt32 → UInt32) : Nat → State → State
  | 0,     s => s
  | n + 1, s => stepN code n (step code s)

@[simp] theorem stepN_zero (code : UInt32 → UInt32) (s : State) :
    stepN code 0 s = s := rfl

@[simp] theorem stepN_succ (code : UInt32 → UInt32) (n : Nat) (s : State) :
    stepN code (n + 1) s = stepN code n (step code s) := rfl

/-- Steps add: taking `n + m` steps is the same as `n` steps followed
    by `m` more. -/
theorem stepN_add (code : UInt32 → UInt32) (n m : Nat) (s : State) :
    stepN code (n + m) s = stepN code m (stepN code n s) := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add, stepN_succ, stepN_succ]
    exact ih (step code s)

/-! ## CFG-level Hoare triple. -/

/-- A CFG-level Hoare triple: from any state satisfying the
    precondition `P`, after some finite number of `step`s the relation
    `R` between the entry and reached state holds.

    Because `step` is total and deterministic, the existential `∃ n`
    captures the *termination* claim — and uniquely determines `s'`. -/
def CFG (code : UInt32 → UInt32) (P : State → Prop) (R : State → State → Prop) : Prop :=
  ∀ s, P s → ∃ n, R s (stepN code n s)

/-! ## Identity + sequential composition. -/

/-- Trivial CFG: reaching `s` from `s` in 0 steps, carrying any
    precondition into the post-relation. -/
theorem CFG.refl (code : UInt32 → UInt32) (P : State → Prop) :
    CFG code P (fun s s' => s = s' ∧ P s) :=
  fun s hP => ⟨0, rfl, hP⟩

/-- Sequential composition (the CFG analogue of `Triple.append`).

    Given two CFG fragments and a way to thread the intermediate
    predicate `Q` (from `R₁`'s post to `R₂`'s pre), their composition
    is a CFG with relation `RComp R₁ R₂`. -/
theorem CFG.trans {code : UInt32 → UInt32} {P Q : State → Prop}
    {R₁ R₂ : State → State → Prop}
    (h₁ : CFG code P R₁) (h_mid : ∀ s s', R₁ s s' → Q s') (h₂ : CFG code Q R₂) :
    CFG code P (RComp R₁ R₂) := by
  intro s hP
  obtain ⟨n1, hR1⟩ := h₁ s hP
  obtain ⟨n2, hR2⟩ := h₂ (stepN code n1 s) (h_mid s _ hR1)
  refine ⟨n1 + n2, stepN code n1 s, hR1, ?_⟩
  rw [stepN_add]; exact hR2

/-! ## Bridge from `Triple` to `CFG`.

`Triple block R` says `R s (runInstrs s block)` — but `runInstrs` is a
fold over a fixed list, oblivious to pc.  To lift this to a CFG
statement we need: starting at some pc, `code` should produce exactly
the instructions of `block`, in order, as we step through.

Crucially, this includes BRANCHING instructions: if `block`'s i-th
instruction is a branch, then `exec` updates pc to the branch target,
and we need `code` at the *new* pc to match `block[i+1]`.  In a
well-formed basic block (one with only an end-of-block branch), the
mid-block pcs are `entry, entry+4, entry+8, …`, and the branch (if any)
is the last instruction — its pc effect happens *after* the block.

We capture this directly by induction on the list. -/

/-- "Starting at state `s`, the `code` matches the instruction list
    `block` as we step through": each next instruction is `block[0]`,
    and after executing it the rest of `block` is at the new pc. -/
def CodeMatchesBlock (code : UInt32 → UInt32) (s : State) : List Instr → Prop
  | []      => True
  | i :: is => decode (code s.pc) = i ∧ CodeMatchesBlock code (exec s i) is

/-- Composition: matching `b1 ++ b2` is matching `b1` from `s`, then `b2`
    from the post-`b1` state `runInstrs s b1`. -/
theorem CodeMatchesBlock_append (code : UInt32 → UInt32) (s : State) (b1 b2 : List Instr)
    (h1 : CodeMatchesBlock code s b1)
    (h2 : CodeMatchesBlock code (runInstrs s b1) b2) :
    CodeMatchesBlock code s (b1 ++ b2) := by
  induction b1 generalizing s with
  | nil => exact h2
  | cons i is ih =>
    refine ⟨h1.1, ih (exec s i) h1.2 ?_⟩
    show CodeMatchesBlock code (runInstrs (exec s i) is) b2
    exact h2

/-- Stepping `block.length` times under `code` is exactly running the
    list via `runInstrs`, provided `code` matches the block as we go. -/
theorem stepN_eq_runInstrs (code : UInt32 → UInt32) (s : State) (block : List Instr)
    (h : CodeMatchesBlock code s block) :
    stepN code block.length s = runInstrs s block := by
  induction block generalizing s with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨h_decode, h_rest⟩ := h
    show stepN code is.length (step code s) = runInstrs (exec s i) is
    have h_step : step code s = exec s i := by
      unfold step; rw [h_decode]
    rw [h_step]
    exact ih (exec s i) h_rest

/-- **The bridge**: any `Triple block R` lifts to a CFG fragment whose
    pre-condition asserts the code-block correspondence. -/
theorem CFG_of_Triple {code : UInt32 → UInt32} {block : List Instr}
    {R : State → State → Prop} (h_block : Triple block R) :
    CFG code (fun s => CodeMatchesBlock code s block) R := by
  intro s h_code
  refine ⟨block.length, ?_⟩
  rw [stepN_eq_runInstrs code s block h_code]
  exact h_block s

/-- Variant of the bridge that pins the entry `pc` to a literal `pc0`.
    Useful for CFG composition where the next block's entry is known. -/
theorem CFG_of_Triple_at {code : UInt32 → UInt32} {block : List Instr}
    {R : State → State → Prop} (pc0 : UInt32)
    (h_block : Triple block R)
    (h_code : ∀ s, s.pc = pc0 → CodeMatchesBlock code s block) :
    CFG code (fun s => s.pc = pc0) R := fun s h_pc =>
  CFG_of_Triple h_block s (h_code s h_pc)

/-! ## Generic loop combinator (Hoare while-rule, do-while flavour).

Captures the textbook proof obligation for do-while loops:

  ```
  { Inv 0 }      <-- after `init`
  while (continue?) {                 <-- bne stays taken
    body
    { Inv (k+1) }
  }
  { Q }                                <-- after `exit`
  ```

For the binary's loops (which all use a bottom-test bne), this folds
"K-1 step applications + 1 exit application" into one combinator call.
The user provides four obligations; the induction over `k` is hidden. -/

/-- Helper for `do_while`: given `Inv s_entry j` and `j + remaining = K - 1`,
    chain `remaining` applications of `h_step` followed by one of
    `h_exit` to reach `Q s_entry _`. -/
private theorem do_while_aux {code : UInt32 → UInt32}
    {K : State → Nat}
    {Inv : State → Nat → State → Prop}
    {Q : State → State → Prop}
    (h_step : ∀ s_entry k, k + 1 < K s_entry →
              CFG code (Inv s_entry k) (fun _ s' => Inv s_entry (k + 1) s'))
    (h_exit : ∀ s_entry, 0 < K s_entry →
              CFG code (Inv s_entry (K s_entry - 1))
                       (fun _ s' => Q s_entry s'))
    (s_entry : State) (h_K_pos : 0 < K s_entry) :
    ∀ (remaining j : Nat), j + remaining = K s_entry - 1 →
      CFG code (Inv s_entry j) (fun _ s' => Q s_entry s') := by
  intro remaining
  induction remaining with
  | zero =>
    intro j h_eq
    have h_j : j = K s_entry - 1 := by omega
    rw [h_j]
    exact h_exit s_entry h_K_pos
  | succ m ih =>
    intro j h_eq
    have h_lt : j + 1 < K s_entry := by omega
    have h_eq' : (j + 1) + m = K s_entry - 1 := by omega
    have ih_inst := ih (j + 1) h_eq'
    have step_inst := h_step s_entry j h_lt
    intro s h_inv_j
    obtain ⟨n1, h_inv_jp1⟩ := step_inst s h_inv_j
    obtain ⟨n2, h_q⟩ := ih_inst (stepN code n1 s) h_inv_jp1
    refine ⟨n1 + n2, ?_⟩
    rw [stepN_add]
    exact h_q

/-- Do-while CFG loop rule.

  - `P` — precondition at the loop entry.
  - `K s` — number of body iterations (function of the entry state).
  - `Inv s_entry k s_curr` — invariant: with respect to entry state
    `s_entry`, after `k` body iterations, the current state is `s_curr`.
  - `Q s_entry s_exit` — post-relation between entry and exit.
  - `h_init` — from `P`, after some steps reach `Inv s 0 _`.
  - `h_step` — when `k + 1 < K`, the body brings `Inv k` → `Inv (k+1)`.
  - `h_exit` — on the final iteration (`k = K - 1`), the body brings
    `Inv (K - 1)` → `Q`.
  - `h_K_pos` — under `P`, `K ≥ 1` (do-while loops run at least once). -/
theorem CFG.do_while {code : UInt32 → UInt32}
    {P : State → Prop}
    {K : State → Nat}
    {Inv : State → Nat → State → Prop}
    {Q : State → State → Prop}
    (h_init : CFG code P (fun s s' => Inv s 0 s'))
    (h_step : ∀ s_entry k, k + 1 < K s_entry →
              CFG code (Inv s_entry k) (fun _ s' => Inv s_entry (k + 1) s'))
    (h_exit : ∀ s_entry, 0 < K s_entry →
              CFG code (Inv s_entry (K s_entry - 1))
                       (fun _ s' => Q s_entry s'))
    (h_K_pos : ∀ s, P s → 0 < K s) :
    CFG code P Q := by
  intro s hP
  have h_K_pos_s : 0 < K s := h_K_pos s hP
  obtain ⟨n_init, h_inv_0⟩ := h_init s hP
  obtain ⟨n_rest, h_q⟩ :=
    do_while_aux h_step h_exit s h_K_pos_s (K s - 1) 0 (by omega)
      (stepN code n_init s) h_inv_0
  refine ⟨n_init + n_rest, ?_⟩
  rw [stepN_add]
  exact h_q

end MemcpyProof.Hoare
