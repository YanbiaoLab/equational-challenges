-- Equation48248 → Equation59606
-- Recorded verdict: true
-- Premise: x * y = (z * (x * w)) * (u * u)
-- Conclusion: (x * y) * z = x * ((y * w) * w)
-- Original submission SHA-256: dd8bef0c484a22335a08cf2d6b816d0f9d53854a45608e9b88e3edaf74086036
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (x ◇ w)) ◇ (u ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = x ◇ ((y ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y x x x).trans ((h x x x x x).symm)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((congrArg (fun t => t ◇ (q0 ◇ q0)) (apc0 q0 q0 (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0))).trans (apc0 (q0 ◇ q0) (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans ((((congrArg (fun t => t ◇ (q0 ◇ q0)) ((h q0 q0 q0 q0 q1).symm)).symm).trans ((h q1 q0 (q0 ◇ (q0 ◇ q0)) q1 q0).symm)).trans (apc0 q1 q0 (q1 ◇ q0) (q1 ◇ q0) (q1 ◇ q0)))
  have apc2 : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((apc1 q0 q1).symm).trans (apc1 q0 q0)
  have apc4 : forall (q2 q3 q4 q5:G), ((q5 ◇ q5) ◇ (q3 ◇ q3)) = ((q2 ◇ q2) ◇ q4):=by
    intro q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q3 ◇ q3)) (apc0 q5 (q2 ◇ q2) (q5 ◇ (q2 ◇ q2)) (q5 ◇ (q2 ◇ q2)) (q5 ◇ (q2 ◇ q2)))).symm).trans (((congrArg (fun t => t ◇ (q3 ◇ q3)) (congrArg (fun t => q5 ◇ t) (apc1 q2 q2))).symm).trans ((h (q2 ◇ q2) q4 q5 (q2 ◇ q2) q3).symm))
  have apc5 : forall (q6 q7 q8:G), ((q6 ◇ q6) ◇ q7) = (q8 ◇ q8):=by
    intro q6 q7 q8
    exact ((apc4 q6 q6 q7 q6).symm).trans (apc2 q8 (q6 ◇ q6))
  have apc37 : forall (q9 q10 q11:G), (((q9 ◇ q9) ◇ (q9 ◇ q9)) ◇ q10) = (q11 ◇ q11):=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ q10) ((apc1 q9 q9).symm)).symm).trans (apc5 q9 q10 q11)
  have apc38 : forall (q12 q13 q14:G), (q14 ◇ q14) = (q13 ◇ q12):=by
    intro q12 q13 q14
    exact ((h q13 q12 (q13 ◇ q13) q13 q12).trans (apc37 q13 (q12 ◇ q12) q14)).symm
  exact ((apc38 z (x ◇ y) ((x ◇ y) ◇ z)).symm).trans (apc38 ((y ◇ w) ◇ w) x ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48248_to_59606 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48248_to_59606
