-- Equation4753 → Equation54740
-- Recorded verdict: false
-- Premise: x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ x))))
-- Conclusion: x ◇ (x ◇ y) = x ◇ ((x ◇ y) ◇ y)
-- Original submission SHA-256: aab97967ec1ae0c18ad046be5b1d4bb272c096eb2b08035f6ad0ae8a1cb1d834
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = x ◇ ((x ◇ y) ◇ y)
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
    op := MemoFinOp.base36TableV2 "223DA00330E085D00BHGA0AAAB051BCC8500FB1G204GG20015G28900HBHGA039G0C03B6C86006B6GA3JHA0C0406485006B6GA3AIG00J55CA85070BAG72JIG00J406786006B6GA0AGGI00G0H789G0HBHG89JIII081FG089I0IBFG72J9A20J107789079B1GA0AAA0B81AG189I0IB1G833DGBB8DBG089G0DB1GA0JGG000G0CC8900HB1GA03IABB0DBHC8907IB1GA33HA0CEE0HE86006BAG20JHG0021FH08920FB1G72JGG212G1G285G70B1GA4JDG00010H189G0HBHG82JHG2BJ107J8607IB1GA0AHI0C010CJ85I0IBHG"
  }
  refine ⟨Fin 20, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4753_to_54740 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4753_to_54740
