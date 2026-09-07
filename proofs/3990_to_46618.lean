-- Equation3990 → Equation46618
-- Recorded verdict: true
-- Premise: x * y = (z * (x * x)) * z
-- Conclusion: x * y = (z * z) * (z * (z * w))
-- Original submission SHA-256: 1a614c6af41a6d7b1365764daf931bfb990b3ff18d26ce752c3e37824b0af007
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (x ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ (z ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ ((q2 ◇ q2) ◇ (q0 ◇ q0))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ (q0 ◇ q0))) ((h q0 q1 (q2 ◇ q2)).symm)).symm).trans ((h q2 q3 ((q2 ◇ q2) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc2 : forall (x y z q0 q1 q2 q3:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q2 ◇ q2):=by
    intro x y z q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ (q0 ◇ q0))) (apc1 q0 q1 (q0 ◇ q1))).trans (apc1 (q0 ◇ q0) ((q2 ◇ q2) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ ((q2 ◇ q2) ◇ (q0 ◇ q0))))).symm).trans ((apc0 q0 q1 q2 q3).trans (apc1 q2 q3 (q2 ◇ q3)))
  have apc3 : forall (q4 q5 q6:G), ((q5 ◇ q5) ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5 q6
    exact (((congrArg (fun t => t ◇ q5) (apc1 q5 (q4 ◇ q4) q4)).symm).trans ((h q4 q6 q5).symm)).trans (apc1 q4 q6 (q4 ◇ q6))
  have apc4 : forall (q7 q8 q9:G), ((q8 ◇ q8) ◇ (q7 ◇ q7)) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ (q7 ◇ q7)) (apc2 q7 q7 q7 q7 q7 q8 q7)).symm).trans (apc3 q9 (q7 ◇ q7) q7)
  have apc20 : forall (q10 q11 q12:G), (q12 ◇ q12) = (q11 ◇ q10):=by
    intro q10 q11 q12
    exact ((h q11 q10 (q11 ◇ q11)).trans (apc4 q11 (q11 ◇ q11) q12)).symm
  exact ((apc20 y x (x ◇ y)).symm).trans (apc20 (z ◇ (z ◇ w)) (z ◇ z) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3990_to_46618 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3990_to_46618
