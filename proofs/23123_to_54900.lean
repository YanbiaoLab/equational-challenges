-- Equation23123 → Equation54900
-- Recorded verdict: false
-- Premise: x = ((x ◇ x) ◇ x) ◇ (y ◇ (z ◇ x))
-- Conclusion: x ◇ (y ◇ x) = x ◇ ((y ◇ y) ◇ x)
-- Original submission SHA-256: 18a1c0cb92ed9b79672fe3abc7834396373bd70a9835d607a18a918daa4a1533
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ x) ◇ x) ◇ (y ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = x ◇ ((y ◇ y) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                             
                              
namespace submission
inductive C | c0 | c1 | c2 deriving DecidableEq
def rot : C → C
  | .c0 => .c1
  | .c1 => .c2
  | .c2 => .c0
abbrev M := Nat × C
def op (a b : M) : M :=
  (if a.2 = b.2 then a.1 + 2 else if a.1 = 0 then b.1 else a.1 - 1, rot (b.2))
instance instMagma : Magma M where op := op
theorem source_holds : @EquationLHS M instMagma := by
  intro q0 q1 q2
  change q0 = (op (op (op q0 q0) q0) (op q1 (op q2 q0)))
  rcases q0 with ⟨n0, s0⟩
  rcases q1 with ⟨n1, s1⟩
  rcases q2 with ⟨n2, s2⟩
  cases s0 <;> cases s1 <;> cases s2 <;>
    simp [op, rot] <;> split_ifs <;> omega
theorem target_fails : ¬ @EquationRHS M instMagma := by
  intro target
  have bad := target ((0, .c0) : M) ((0, .c0) : M)
  exact (by decide : (op ((0, .c0) : M) (op ((0, .c0) : M) ((0, .c0) : M))) ≠ (op ((0, .c0) : M) (op (op ((0, .c0) : M) ((0, .c0) : M)) ((0, .c0) : M)))) bad
end submission
def submission : Goal :=
  ⟨submission.M, submission.instMagma,
   submission.source_holds, submission.target_fails⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23123_to_54900 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_23123_to_54900
