-- Equation45405 → Equation50667
-- Recorded verdict: false
-- Premise: x ◇ y = y ◇ (((x ◇ y) ◇ y) ◇ y)
-- Conclusion: x ◇ y = (y ◇ ((x ◇ y) ◇ y)) ◇ y
-- Original submission SHA-256: a4fe92d0d8ad62f59794122da1f7281c51de7c567a26ba51be663b40b649cdc3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = y ◇ (((x ◇ y) ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ ((x ◇ y) ◇ y)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
                             
                              

namespace submission

inductive C | c0 | c1 deriving DecidableEq
abbrev M := Nat × C

def val (a : Nat) (s : C) (b : Nat) (t : C) : Nat :=
  match s, t with
  | .c0, .c0 => if a ≤ b then a else b
  | .c0, .c1 => a + 1
  | .c1, .c0 => b - 2
  | .c1, .c1 => 0

def ctrl (s t : C) : C :=
  match s, t with
  | .c0, .c0 => .c0
  | .c0, .c1 => .c0
  | .c1, .c0 => .c0
  | .c1, .c1 => .c0

def op (x y : M) : M :=
  (val x.1 x.2 y.1 y.2, ctrl x.2 y.2)

instance instMagma : Magma M where op := op

theorem source_holds : @EquationLHS M instMagma := by
  intro x y
  change op (x) (y) = op (y) (op (op (op (x) (y)) (y)) (y))
  rcases x with ⟨n0, s0⟩
  rcases y with ⟨n1, s1⟩
  cases s0 <;> cases s1 <;>
    simp [op, val, ctrl] <;> (try split_ifs) <;> omega

theorem target_fails : ¬ @EquationRHS M instMagma := by
  intro target
  have bad := target ((0, .c1) : M) ((0, .c1) : M)
  exact
    (by decide :
      op (((0, .c1) : M)) (((0, .c1) : M)) ≠
      op (op (((0, .c1) : M)) (op (op (((0, .c1) : M)) (((0, .c1) : M))) (((0, .c1) : M)))) (((0, .c1) : M))) bad

end submission

def submission : Goal :=
  ⟨submission.M, submission.instMagma,
   submission.source_holds, submission.target_fails⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45405_to_50667 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_45405_to_50667
