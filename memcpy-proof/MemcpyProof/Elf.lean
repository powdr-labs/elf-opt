/-
Minimal ELF32 little-endian reader.

We only support what we need: open an ELF32-LE file, walk its section
headers and symbol table, locate a function symbol by name, and return
the raw bytes of that function from its containing section.

This is intentionally small (~150 lines) so the proof project can be
read end-to-end. If you want a fuller parser, see ELFSage on GitHub.
-/

namespace MemcpyProof.Elf

structure SectionHeader where
  name     : UInt32  -- offset into the section-header string table
  type     : UInt32
  flags    : UInt32
  addr     : UInt32  -- vaddr where this section is loaded
  offset   : UInt32  -- offset of section content in the file
  size     : UInt32
  link     : UInt32
  info     : UInt32
  addralign: UInt32
  entsize  : UInt32
  deriving Repr, Inhabited

structure Symbol where
  name  : UInt32   -- offset into the linked string table
  value : UInt32   -- virtual address for executables
  size  : UInt32
  info  : UInt8
  other : UInt8
  shndx : UInt16
  deriving Repr, Inhabited

structure Elf where
  bytes      : ByteArray
  shoff      : UInt32   -- section header table offset
  shentsize  : UInt16
  shnum      : UInt16
  shstrndx   : UInt16
  sections   : Array SectionHeader

def u16le (b : ByteArray) (i : Nat) : UInt16 :=
  let lo := (b.get! i).toUInt16
  let hi := (b.get! (i+1)).toUInt16
  lo ||| (hi <<< 8)

def u32le (b : ByteArray) (i : Nat) : UInt32 :=
  let b0 := (b.get! i).toUInt32
  let b1 := (b.get! (i+1)).toUInt32
  let b2 := (b.get! (i+2)).toUInt32
  let b3 := (b.get! (i+3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

def parseHeader (b : ByteArray) : Except String Elf := do
  if b.size < 52 then throw "ELF too short"
  if !(b.get! 0 == 0x7f && b.get! 1 == 0x45 && b.get! 2 == 0x4c && b.get! 3 == 0x46) then
    throw "not an ELF magic"
  if b.get! 4 != 1 then throw "not ELF32"
  if b.get! 5 != 1 then throw "not little-endian"
  let shoff     := u32le b 0x20
  let shentsize := u16le b 0x2e
  let shnum     := u16le b 0x30
  let shstrndx  := u16le b 0x32
  if shentsize.toNat != 40 then throw s!"unexpected shentsize {shentsize}"
  let mut shs : Array SectionHeader := Array.mkEmpty shnum.toNat
  for i in [0:shnum.toNat] do
    let base := shoff.toNat + i * shentsize.toNat
    shs := shs.push {
      name      := u32le b base
      type      := u32le b (base + 4)
      flags     := u32le b (base + 8)
      addr      := u32le b (base + 12)
      offset    := u32le b (base + 16)
      size      := u32le b (base + 20)
      link      := u32le b (base + 24)
      info      := u32le b (base + 28)
      addralign := u32le b (base + 32)
      entsize   := u32le b (base + 36)
    }
  return { bytes := b, shoff, shentsize, shnum, shstrndx, sections := shs }

def readCString (b : ByteArray) (start : Nat) : String := Id.run do
  let mut i := start
  let mut acc : String := ""
  while i < b.size && b.get! i != 0 do
    acc := acc.push (Char.ofUInt8 (b.get! i))
    i := i + 1
  return acc
where
  Char.ofUInt8 (x : UInt8) : Char := Char.ofNat x.toNat

/-- Resolve a section-header `name` field into a string using the
shstrtab (section header at index `shstrndx`). -/
def sectionName (e : Elf) (sh : SectionHeader) : String :=
  let strtab := e.sections[e.shstrndx.toNat]!
  readCString e.bytes (strtab.offset.toNat + sh.name.toNat)

def findSection (e : Elf) (name : String) : Option SectionHeader :=
  e.sections.find? (fun sh => sectionName e sh == name)

/-- Walk a SHT_SYMTAB section, returning the parsed symbols and the
linked string table (for symbol-name resolution). -/
def readSymbols (e : Elf) (symtab : SectionHeader) :
    Array Symbol × SectionHeader := Id.run do
  let strtab := e.sections[symtab.link.toNat]!
  let n := symtab.size.toNat / symtab.entsize.toNat
  let mut syms : Array Symbol := Array.mkEmpty n
  for i in [0:n] do
    let base := symtab.offset.toNat + i * symtab.entsize.toNat
    syms := syms.push {
      name  := u32le e.bytes base
      value := u32le e.bytes (base + 4)
      size  := u32le e.bytes (base + 8)
      info  := e.bytes.get! (base + 12)
      other := e.bytes.get! (base + 13)
      shndx := u16le e.bytes (base + 14)
    }
  return (syms, strtab)

/-- Find a symbol by name across .symtab. -/
def findSymbol (e : Elf) (name : String) : Option Symbol := Id.run do
  let symtab? := e.sections.find? (fun sh => sh.type == 2)  -- SHT_SYMTAB
  match symtab? with
  | none        => return none
  | some symtab =>
    let (syms, strtab) := readSymbols e symtab
    for s in syms do
      if readCString e.bytes (strtab.offset.toNat + s.name.toNat) == name then
        return some s
    return none

/-- Given a function symbol, return its bytes by locating the section that
contains its virtual address and slicing. The size is taken either from the
symbol itself (if non-zero) or from a caller-supplied `fallbackSize`. -/
def symbolBytes (e : Elf) (s : Symbol) (fallbackSize : Nat := 0) :
    Except String ByteArray := do
  let size := if s.size.toNat == 0 then fallbackSize else s.size.toNat
  -- find a PROGBITS+ALLOC section that contains this vaddr
  let some sh := e.sections.find? (fun sh =>
        sh.type == 1 &&  -- PROGBITS
        s.value ≥ sh.addr &&
        s.value + size.toUInt32 ≤ sh.addr + sh.size)
    | throw s!"no section contains symbol at 0x{toString s.value}"
  let fileOff := sh.offset.toNat + (s.value.toNat - sh.addr.toNat)
  return e.bytes.extract fileOff (fileOff + size)

end MemcpyProof.Elf
