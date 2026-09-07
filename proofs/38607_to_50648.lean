-- Equation38607 → Equation50648
-- Recorded verdict: true
-- Premise: x = ((y * ((z * y) * x)) * y) * x
-- Conclusion: x * y = (x * ((z * w) * u)) * y
-- Original submission SHA-256: ba4595d754e9d349d17b37102629e91eb4922ee7ddb9fbd2a6c9ad2825230eae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ ((z ◇ y) ◇ x)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (x ◇ ((z ◇ w) ◇ u)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), (((q1 ◇ q0) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q1) (congrArg (fun t => q1 ◇ t) ((h q0 q1 q0).symm)))).symm).trans ((h q0 q1 (q1 ◇ ((q0 ◇ q1) ◇ q0))).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ ((q2 ◇ q3) ◇ q2)) ◇ q3) = q3:=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ ((q2 ◇ q3) ◇ q2)) (apc0 q3 q2))).symm).trans (apc0 q3 ((q2 ◇ q3) ◇ q2))
  have apc2 : forall (q4 q5:G), (q5 ◇ q4) = q4:=by
    intro q4 q5
    exact ((congrArg (fun t => t ◇ q4) (apc1 q4 q5)).symm).trans ((h q4 q5 q4).symm)
  exact (apc2 y x).trans ((apc2 y (x ◇ ((z ◇ w) ◇ u))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38607_to_50648 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38607_to_50648
