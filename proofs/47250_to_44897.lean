-- Equation47250 → Equation44897
-- Recorded verdict: true
-- Premise: x * y = (y * z) * ((y * w) * z)
-- Conclusion: x * y = z * ((w * (x * x)) * y)
-- Original submission SHA-256: 5c695540d4624f2c113dd4e2e148b0be1584e6766e2384e4caf99607a96c6b3b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ ((y ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ (x ◇ x)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6 q7:G), (q3 ◇ ((q6 ◇ q4) ◇ q7)) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6 q7
    exact ((apc1 q3 (q6 ◇ q7) ((q6 ◇ q4) ◇ q7)).symm).trans ((h q5 q6 q7 q4).symm)
  have apc8 : forall (q8 q9 q10 q11:G), (q8 ◇ (q11 ◇ q11)) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => q8 ◇ t) ((apc0 (q10 ◇ q8) q11 q8 q8).symm)).symm).trans (apc2 q8 q8 q9 q10 q11)
  exact ((apc8 (z ◇ ((w ◇ (x ◇ x)) ◇ y)) x y (x ◇ y)).symm).trans (apc8 (z ◇ ((w ◇ (x ◇ x)) ◇ y)) z ((w ◇ (x ◇ x)) ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47250_to_44897 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47250_to_44897
