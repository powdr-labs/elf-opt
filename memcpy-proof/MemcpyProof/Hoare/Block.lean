/-
Straight-line execution over a list of instructions.

`runInstrs s instrs` folds `exec` over the list — no PC dispatch, no `code`,
no `decode`.  This is the foundation for layout-independent reasoning about
basic blocks.

A "basic block" here means: a list of non-branching instructions (i.e., the
list itself describes the next instruction to execute, regardless of what
the previous instruction did to `s.pc`).  Branches are handled at a higher
level (a CFG combinator yet to be added).
-/

import MemcpyProof.Sem

namespace MemcpyProof.Hoare

open MemcpyProof.Sem
open MemcpyProof.RV32I

/-- Run a list of instructions in order, stopping early if `halted` is set. -/
def runInstrs (s : State) : List Instr → State
  | []      => s
  | i :: is => if s.halted then s else runInstrs (exec s i) is

@[simp] theorem runInstrs_nil (s : State) : runInstrs s [] = s := rfl

theorem runInstrs_cons (s : State) (i : Instr) (is : List Instr) :
    runInstrs s (i :: is) = if s.halted then s else runInstrs (exec s i) is := rfl

@[simp] theorem runInstrs_cons_not_halted (s : State) (i : Instr) (is : List Instr)
    (h : s.halted = false) :
    runInstrs s (i :: is) = runInstrs (exec s i) is := by
  rw [runInstrs_cons, h]; rfl

/-- `runInstrs` distributes over list concatenation when the first part
    doesn't halt.  This is the semantic underpinning of the Hoare `seq` rule. -/
theorem runInstrs_append (s : State) (b1 b2 : List Instr) :
    runInstrs s (b1 ++ b2) = runInstrs (runInstrs s b1) b2 := by
  induction b1 generalizing s with
  | nil => simp
  | cons i is ih =>
    show runInstrs s (i :: (is ++ b2)) = runInstrs (runInstrs s (i :: is)) b2
    by_cases h : s.halted = true
    · -- If halted, runInstrs s _ = s for any list.
      have h_any : ∀ l, runInstrs s l = s := by
        intro l
        cases l with
        | nil => rfl
        | cons _ _ => unfold runInstrs; rw [h]; rfl
      rw [h_any (i :: (is ++ b2)), h_any (i :: is), h_any b2]
    · -- Not halted: peel one step and recurse.
      have h_false : s.halted = false := by
        cases hb : s.halted
        · rfl
        · exact absurd hb h
      rw [runInstrs_cons_not_halted _ _ _ h_false,
          runInstrs_cons_not_halted _ _ _ h_false]
      exact ih (exec s i)

end MemcpyProof.Hoare
