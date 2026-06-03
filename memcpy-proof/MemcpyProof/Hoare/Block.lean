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

/-- Run a list of instructions in order. -/
def runInstrs (s : State) : List Instr → State
  | []      => s
  | i :: is => runInstrs (exec s i) is

@[simp] theorem runInstrs_nil (s : State) : runInstrs s [] = s := rfl

@[simp] theorem runInstrs_cons (s : State) (i : Instr) (is : List Instr) :
    runInstrs s (i :: is) = runInstrs (exec s i) is := rfl

/-- `runInstrs` distributes over list concatenation.  This is the semantic
    underpinning of the Hoare `seq` rule. -/
theorem runInstrs_append (s : State) (b1 b2 : List Instr) :
    runInstrs s (b1 ++ b2) = runInstrs (runInstrs s b1) b2 := by
  induction b1 generalizing s with
  | nil => simp
  | cons i is ih => simp [runInstrs_cons]; exact ih (exec s i)

end MemcpyProof.Hoare
