-- Equation45552 → Equation60949
-- Recorded verdict: true
-- Premise: x * y = z * (((x * x) * z) * z)
-- Conclusion: (x * x) * y = (z * (x * x)) * x
-- Original submission SHA-256: 979152da61e597e7e879515d58a9a147eee113dd82c6f4a8b0771c15cc161804
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (((x ◇ x) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (z ◇ (x ◇ x)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0).trans ((h q1 q2 q0).symm)).symm
  have apc1 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ q3) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((apc0 q3 q5 (((q4 ◇ q4) ◇ q5) ◇ q5)).symm).trans ((h q4 q6 q5).symm)).trans (apc1 q4 q6 (q4 ◇ q6))
  exact (apc2 y ((x ◇ x) ◇ y) (x ◇ x) ((x ◇ x) ◇ y)).trans ((apc2 x ((x ◇ x) ◇ y) (z ◇ (x ◇ x)) ((x ◇ x) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45552_to_60949 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45552_to_60949
