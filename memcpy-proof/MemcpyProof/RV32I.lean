/-
Minimal RV32I (and a few RV32M) decoder + small-step semantics.

Scope: enough to faithfully execute the `memcpy` function extracted from
`client.elf`. We support the I/S/B/U/J instruction shapes, base ALU, loads,
stores, branches, jumps, and a handful of M-ext multiplications.

Inspired by — but not depending on — the RV32 model in risc0-lean4.  We
write our own here both because that project pins a 2022 Lean nightly
and because we want a tight kernel-reducible interpreter for proofs.
-/

namespace MemcpyProof.RV32I

/-- A RISC-V register index — 0..31.  Defined here so that `Instr`'s
register-operand fields are bounded by construction. -/
abbrev Reg := Fin 32

/-! ## Bit-extraction helpers (all over `UInt32`). -/

@[reducible] def bits (w : UInt32) (lo hi : Nat) : UInt32 :=
  (w >>> lo.toUInt32) &&& ((1 <<< (hi - lo + 1).toUInt32) - 1)

@[reducible] def signExt (x : UInt32) (signBit : Nat) : UInt32 :=
  let m : UInt32 := 1 <<< signBit.toUInt32
  (x ^^^ m) - m

@[reducible] def opcode (w : UInt32) : UInt32 := bits w 0 6
@[reducible] def rd    (w : UInt32) : Reg :=
  ⟨(bits w 7 11).toNat % 32, Nat.mod_lt _ (by decide)⟩
@[reducible] def funct3 (w : UInt32) : UInt32 := bits w 12 14
@[reducible] def rs1   (w : UInt32) : Reg :=
  ⟨(bits w 15 19).toNat % 32, Nat.mod_lt _ (by decide)⟩
@[reducible] def rs2   (w : UInt32) : Reg :=
  ⟨(bits w 20 24).toNat % 32, Nat.mod_lt _ (by decide)⟩
@[reducible] def funct7 (w : UInt32) : UInt32 := bits w 25 31

@[reducible] def immI (w : UInt32) : UInt32 := signExt (bits w 20 31) 11
@[reducible] def immS (w : UInt32) : UInt32 :=
  signExt ((bits w 25 31 <<< 5) ||| bits w 7 11) 11
@[reducible] def immB (w : UInt32) : UInt32 :=
  let b11 := bits w 7 7
  let b41 := bits w 8 11
  let b105 := bits w 25 30
  let b12  := bits w 31 31
  signExt ((b12 <<< 12) ||| (b11 <<< 11) ||| (b105 <<< 5) ||| (b41 <<< 1)) 12
@[reducible] def immU (w : UInt32) : UInt32 := w &&& 0xfffff000
@[reducible] def immJ (w : UInt32) : UInt32 :=
  let b1912 := bits w 12 19
  let b11   := bits w 20 20
  let b101  := bits w 21 30
  let b20   := bits w 31 31
  signExt ((b20 <<< 20) ||| (b1912 <<< 12) ||| (b11 <<< 11) ||| (b101 <<< 1)) 20

/-! ## Decoded instructions. -/

inductive Instr where
  -- I-type ALU (op-imm)
  | addi  (rd rs1 : Reg) (imm : UInt32)
  | slti  (rd rs1 : Reg) (imm : UInt32)
  | sltiu (rd rs1 : Reg) (imm : UInt32)
  | xori  (rd rs1 : Reg) (imm : UInt32)
  | ori   (rd rs1 : Reg) (imm : UInt32)
  | andi  (rd rs1 : Reg) (imm : UInt32)
  | slli  (rd rs1 : Reg) (shamt : UInt32)
  | srli  (rd rs1 : Reg) (shamt : UInt32)
  | srai  (rd rs1 : Reg) (shamt : UInt32)
  -- R-type ALU (op)
  | add   (rd rs1 rs2 : Reg)
  | sub   (rd rs1 rs2 : Reg)
  | sll   (rd rs1 rs2 : Reg)
  | slt   (rd rs1 rs2 : Reg)
  | sltu  (rd rs1 rs2 : Reg)
  | xor   (rd rs1 rs2 : Reg)
  | srl   (rd rs1 rs2 : Reg)
  | sra   (rd rs1 rs2 : Reg)
  | or_   (rd rs1 rs2 : Reg)
  | and_  (rd rs1 rs2 : Reg)
  -- M-ext (only what memcpy might touch)
  | mul   (rd rs1 rs2 : Reg)
  -- loads
  | lb    (rd rs1 : Reg) (imm : UInt32)
  | lh    (rd rs1 : Reg) (imm : UInt32)
  | lw    (rd rs1 : Reg) (imm : UInt32)
  | lbu   (rd rs1 : Reg) (imm : UInt32)
  | lhu   (rd rs1 : Reg) (imm : UInt32)
  -- stores
  | sb    (rs1 rs2 : Reg) (imm : UInt32)
  | sh    (rs1 rs2 : Reg) (imm : UInt32)
  | sw    (rs1 rs2 : Reg) (imm : UInt32)
  -- branches
  | beq   (rs1 rs2 : Reg) (imm : UInt32)
  | bne   (rs1 rs2 : Reg) (imm : UInt32)
  | blt   (rs1 rs2 : Reg) (imm : UInt32)
  | bge   (rs1 rs2 : Reg) (imm : UInt32)
  | bltu  (rs1 rs2 : Reg) (imm : UInt32)
  | bgeu  (rs1 rs2 : Reg) (imm : UInt32)
  -- jumps + upper-imm
  | jal   (rd : Reg) (imm : UInt32)
  | jalr  (rd rs1 : Reg) (imm : UInt32)
  | lui   (rd : Reg) (imm : UInt32)
  | auipc (rd : Reg) (imm : UInt32)
  -- fence / system / etc. we don't need; encode generically
  | other (raw : UInt32)
  deriving Repr, Inhabited

/-! ## Decoder. -/

@[reducible] def decode (w : UInt32) : Instr :=
  let op := opcode w
  let f3 := funct3 w
  let f7 := funct7 w
  let d  := rd w
  let a  := rs1 w
  let b  := rs2 w
  match op with
  | 0x37 => .lui d (immU w)
  | 0x17 => .auipc d (immU w)
  | 0x6f => .jal d (immJ w)
  | 0x67 => if f3 == 0 then .jalr d a (immI w) else .other w
  | 0x63 =>
    let imm := immB w
    match f3 with
    | 0 => .beq  a b imm
    | 1 => .bne  a b imm
    | 4 => .blt  a b imm
    | 5 => .bge  a b imm
    | 6 => .bltu a b imm
    | 7 => .bgeu a b imm
    | _ => .other w
  | 0x03 =>
    let imm := immI w
    match f3 with
    | 0 => .lb  d a imm
    | 1 => .lh  d a imm
    | 2 => .lw  d a imm
    | 4 => .lbu d a imm
    | 5 => .lhu d a imm
    | _ => .other w
  | 0x23 =>
    let imm := immS w
    match f3 with
    | 0 => .sb a b imm
    | 1 => .sh a b imm
    | 2 => .sw a b imm
    | _ => .other w
  | 0x13 =>
    let imm := immI w
    let shamt := bits w 20 24
    match f3 with
    | 0 => .addi  d a imm
    | 1 => if f7 == 0 then .slli d a shamt else .other w
    | 2 => .slti  d a imm
    | 3 => .sltiu d a imm
    | 4 => .xori  d a imm
    | 5 => if f7 == 0 then .srli d a shamt
           else if f7 == 0x20 then .srai d a shamt else .other w
    | 6 => .ori   d a imm
    | 7 => .andi  d a imm
    | _ => .other w
  | 0x33 =>
    match f3, f7 with
    | 0, 0     => .add  d a b
    | 0, 0x20  => .sub  d a b
    | 1, 0     => .sll  d a b
    | 2, 0     => .slt  d a b
    | 3, 0     => .sltu d a b
    | 4, 0     => .xor  d a b
    | 5, 0     => .srl  d a b
    | 5, 0x20  => .sra  d a b
    | 6, 0     => .or_  d a b
    | 7, 0     => .and_ d a b
    | 0, 1     => .mul  d a b
    | _, _     => .other w
  | _ => .other w

/-! ## Pretty-printing for sanity-checks. -/

def regName (r : Reg) : String :=
  let names := #["zero","ra","sp","gp","tp","t0","t1","t2",
                 "s0","s1","a0","a1","a2","a3","a4","a5",
                 "a6","a7","s2","s3","s4","s5","s6","s7",
                 "s8","s9","s10","s11","t3","t4","t5","t6"]
  names[r.val]!

def signedDec (x : UInt32) : String :=
  if x &&& 0x80000000 != 0 then
    s!"-{(0 - x).toNat}"
  else
    s!"{x.toNat}"

def Instr.pp : Instr → String
  | .addi  d a i => s!"addi  {regName d}, {regName a}, {signedDec i}"
  | .slti  d a i => s!"slti  {regName d}, {regName a}, {signedDec i}"
  | .sltiu d a i => s!"sltiu {regName d}, {regName a}, {signedDec i}"
  | .xori  d a i => s!"xori  {regName d}, {regName a}, {signedDec i}"
  | .ori   d a i => s!"ori   {regName d}, {regName a}, {signedDec i}"
  | .andi  d a i => s!"andi  {regName d}, {regName a}, {signedDec i}"
  | .slli  d a s => s!"slli  {regName d}, {regName a}, {s.toNat}"
  | .srli  d a s => s!"srli  {regName d}, {regName a}, {s.toNat}"
  | .srai  d a s => s!"srai  {regName d}, {regName a}, {s.toNat}"
  | .add   d a b => s!"add   {regName d}, {regName a}, {regName b}"
  | .sub   d a b => s!"sub   {regName d}, {regName a}, {regName b}"
  | .sll   d a b => s!"sll   {regName d}, {regName a}, {regName b}"
  | .slt   d a b => s!"slt   {regName d}, {regName a}, {regName b}"
  | .sltu  d a b => s!"sltu  {regName d}, {regName a}, {regName b}"
  | .xor   d a b => s!"xor   {regName d}, {regName a}, {regName b}"
  | .srl   d a b => s!"srl   {regName d}, {regName a}, {regName b}"
  | .sra   d a b => s!"sra   {regName d}, {regName a}, {regName b}"
  | .or_   d a b => s!"or    {regName d}, {regName a}, {regName b}"
  | .and_  d a b => s!"and   {regName d}, {regName a}, {regName b}"
  | .mul   d a b => s!"mul   {regName d}, {regName a}, {regName b}"
  | .lb    d a i => s!"lb    {regName d}, {signedDec i}({regName a})"
  | .lh    d a i => s!"lh    {regName d}, {signedDec i}({regName a})"
  | .lw    d a i => s!"lw    {regName d}, {signedDec i}({regName a})"
  | .lbu   d a i => s!"lbu   {regName d}, {signedDec i}({regName a})"
  | .lhu   d a i => s!"lhu   {regName d}, {signedDec i}({regName a})"
  | .sb    a b i => s!"sb    {regName b}, {signedDec i}({regName a})"
  | .sh    a b i => s!"sh    {regName b}, {signedDec i}({regName a})"
  | .sw    a b i => s!"sw    {regName b}, {signedDec i}({regName a})"
  | .beq   a b i => s!"beq   {regName a}, {regName b}, {signedDec i}"
  | .bne   a b i => s!"bne   {regName a}, {regName b}, {signedDec i}"
  | .blt   a b i => s!"blt   {regName a}, {regName b}, {signedDec i}"
  | .bge   a b i => s!"bge   {regName a}, {regName b}, {signedDec i}"
  | .bltu  a b i => s!"bltu  {regName a}, {regName b}, {signedDec i}"
  | .bgeu  a b i => s!"bgeu  {regName a}, {regName b}, {signedDec i}"
  | .jal   d   i => s!"jal   {regName d}, {signedDec i}"
  | .jalr  d a i => s!"jalr  {regName d}, {signedDec i}({regName a})"
  | .lui   d   i => s!"lui   {regName d}, 0x{(i >>> 12).toNat |> (Nat.toDigits 16 ·) |>.asString}"
  | .auipc d   i => s!"auipc {regName d}, 0x{(i >>> 12).toNat |> (Nat.toDigits 16 ·) |>.asString}"
  | .other w     => s!"; .word 0x{w.toNat |> (Nat.toDigits 16 ·) |>.asString}"

end MemcpyProof.RV32I
