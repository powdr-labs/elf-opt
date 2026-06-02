import Lake
open Lake DSL

package memcpyProof where
  -- pull in the standard `bv_decide` from Lean's bundled std

-- `Std.Tactic.BVDecide` ships with Lean itself; no `require` needed.

@[default_target]
lean_lib MemcpyProof

@[default_target]
lean_exe extract where
  root := `Main

lean_exe simtest where
  root := `Test
