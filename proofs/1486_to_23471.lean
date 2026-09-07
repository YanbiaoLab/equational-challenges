-- Equation1486 → Equation23471
-- Recorded verdict: false
-- Premise: x = (y ◇ x) ◇ (x ◇ (z ◇ z))
-- Conclusion: x = ((y ◇ y) ◇ x) ◇ (x ◇ (y ◇ z))
-- Original submission SHA-256: c8f8c21f9baf382302b0fa2d0593529c7a747bca22db3067b299ab18c603bdb2
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (x ◇ (z ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ x) ◇ (x ◇ (y ◇ z))
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
-- stage:stage2_formula_cdcl_fin2to11_model_synthesis
                   
                             
                           

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
  let m : Magma (Fin 11) := {
    op := MemoFinOp.base36TableV2 "1757AA257A5633930809906626AA259A214214420912145144857156727AA207A213313020710133138857186656AA259A56339388099864594425995"
  }
  refine ⟨Fin 11, m, ?_⟩
  decideFin!

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1486_to_23471 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1486_to_23471
