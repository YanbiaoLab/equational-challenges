-- Equation3801 → Equation52106
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (w * u)
-- Conclusion: x * x = ((y * (x * x)) * x) * y
-- Original submission SHA-256: 12aeab3fff049a709159209bdf36849f98910ce0d3d2526fd833e5653d853bbe
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ x) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((y ◇ (x ◇ x)) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 (q1 ◇ q0) (q0 ◇ q0) q0 q0 q0).symm).trans ((h q0 q2 q1 q0 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6 q7:G), ((q4 ◇ q3) ◇ q5) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6 q7
    exact ((((apc0 (q3 ◇ q3) (q6 ◇ q7) ((q3 ◇ q3) ◇ (q6 ◇ q7)) ((q3 ◇ q3) ◇ (q6 ◇ q7)) ((q3 ◇ q3) ◇ (q6 ◇ q7))).trans (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ (q6 ◇ q7)) (apc1 q3 q4 q3)).symm).trans ((h (q4 ◇ q3) q5 (q4 ◇ q3) q6 q7).symm))).symm
  exact (apc2 x (y ◇ (x ◇ x)) y (x ◇ x) (x ◇ x)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3801_to_52106 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3801_to_52106
