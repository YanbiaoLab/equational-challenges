-- Equation43709 → Equation54149
-- Recorded verdict: true
-- Premise: x * y = y * ((y * z) * (w * w))
-- Conclusion: x * (y * x) = z * (w * (z * u))
-- Original submission SHA-256: 14e61aa0d549eebad1baea25d8b4f2404a2c86da021942b7ee9df3f59b9d0c25
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((y ◇ z) ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ x) = z ◇ (w ◇ (z ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (q2 ◇ (q0 ◇ (q2 ◇ q3))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 (q2 ◇ q3) (q2 ◇ q3) (q2 ◇ q3)).symm)).symm).trans ((h q1 q2 q3 ((q2 ◇ q3) ◇ (q2 ◇ q3))).symm)
  have apc3 : forall (q4 q5 q6 q7:G), (q7 ◇ (q4 ◇ q5)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q7 ◇ t) (apc2 q7 q4 q5 q4)).symm).trans (apc2 q5 q6 q7 (q5 ◇ q4))
  have apc4 : forall (q8 q9 q10 q11 q12:G), (q11 ◇ (q8 ◇ q9)) = (q10 ◇ q12):=by
    intro q8 q9 q10 q11 q12
    exact (((apc3 q8 q9 q10 q12).symm).trans (apc0 q11 q12 (q8 ◇ q9))).symm
  have apc7 : forall (q8 q10 q12 q9 q11:G), (q10 ◇ q12) = (q8 ◇ q8):=by
    intro q8 q10 q12 q9 q11
    exact ((apc4 q8 q9 q10 q11 q12).symm).trans (apc4 q8 q9 q8 q11 q8)
  exact (apc7 (x ◇ (y ◇ x)) x (y ◇ x) (x ◇ (y ◇ x)) (x ◇ (y ◇ x))).trans ((apc7 (x ◇ (y ◇ x)) z (w ◇ (z ◇ u)) (x ◇ (y ◇ x)) (x ◇ (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43709_to_54149 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43709_to_54149
