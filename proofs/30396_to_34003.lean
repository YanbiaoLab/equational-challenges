-- Equation30396 → Equation34003
-- Recorded verdict: false
-- Premise: x = (y ◇ (x ◇ ((y ◇ z) ◇ z))) ◇ x
-- Conclusion: x = ((y ◇ y) ◇ (x ◇ (y ◇ y))) ◇ x
-- Original submission SHA-256: 4182b6bd39af42a51c45fa6a0b3a8f4c1df95a6c1ff4787a6c38caa2839e69b0
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ ((y ◇ z) ◇ z))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ y) ◇ (x ◇ (y ◇ y))) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Embedded module: JudgeDecide.DecideBang
section
/- decideFin! tactic: decides propositions over finite types by exhaustive checking. -/
           

macro "decideFin!" : tactic => `(tactic| decide)
end

-- Embedded module: JudgeFinOp.MemoFinOp
section
/- finOpTable: build a Magma (Fin n) from a string like "[[0,1],[1,0]]". -/
                       

namespace MemoFinOp

private def extractDigits (s : String) : List Nat :=
  s.toList.filterMap fun c =>
    if c.isDigit then some (c.toNat - '0'.toNat) else none

def finOpTable (s : String) (i j : Fin n) : Fin n :=
  let vals := extractDigits s
  let idx := i.val * n + j.val
  ⟨(vals.getD idx 0) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

end MemoFinOp
end

-- Original submission body
                   
                             
                           
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace MemoFinOp

private def decodeBase36V2 (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else c.toNat - 'A'.toNat + 10

def base36TableV2 (s : String) (i j : Fin n) : Fin n :=
  let vals := s.toList.map decodeBase36V2
  let idx := i.val * n + j.val
  ⟨(vals.getD idx 0) % n,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

end MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 20) := {
    op := MemoFinOp.base36TableV2 "12BEHFF7HFECC21ICD33J60345J78BABCDIIGHGJ0J634FJ7GJDGC4IIGDG8012355A789ABCDEFGHIJJ12H3H6799AHCGEFHE1DJ126HB65HHAGCDEFGEFA0BIG45B787GBD366GH44H1234H6951ABDDEFGHIJJ1234HG79FBGCDEFGGI30B234BB5AAABDDEFGHIJA12345B799ABDDEFGHIJB1I3456789ABCDEFGHIJ012554BD5524936FIH44012G45HD99BB6GEFG8I50J2J45B789JBCD6FGBI80J2348J78JABCDE6GHGJG123456789ABCDEFGHIJH123456789ABCDEFGHIJ0H6345D78ADHCDIIHH3JG12345G789ABCDEFGHIJ"
  }
  refine ⟨Fin 20, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30396_to_34003 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_30396_to_34003
