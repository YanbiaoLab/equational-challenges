-- Equation6580 → Equation27694
-- Recorded verdict: false
-- Premise: x = x * (y * ((z * x) * (y * y)))
-- Conclusion: x = ((x * (y * z)) * w) * (u * x)
-- Original submission SHA-256: 583fa0c929422f8e9cdc9931bd8424c5084216623384c45536d1be1325baa1ea
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((z ◇ x) ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((x ◇ (y ◇ z)) ◇ w) ◇ (u ◇ x)
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
    op := MemoFinOp.base36TableV2 "83J002BHB4J1F2H000H018H11CIBA4J1FCG111114E8222BHB4J1F2H222F213133CIBA41FFCG3441344148CIBA4J1FCG44444554H0E0C9FG0GAA5J15H664H007C9IHJ4AA6F16H4E1072B5B01735H777F2884J8CIBEFGJHCG8J18J99J9000C97934A29F1994E1AA2BHB45032H0AAFABB1B0IAGCF4DJ99000BB4ECCCIAGC0F16990C0JC4D1FDCIBA01D35GDDDFJ4E1CEIAGC0F1F960EEJCFF1FFCIBA4J1FCG8FFFFGG1G000C9F40JA2GD0GGHH1H000C9F40JA2H0DHH4J4II2BHB4J1F2HIII8I1J1JJCIBA41FFCGJ441J"
  }
  refine ⟨Fin 20, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6580_to_27694 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_6580_to_27694
