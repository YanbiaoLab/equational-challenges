-- Equation22769 → Equation60919
-- Recorded verdict: true
-- Premise: x = (y * (z * x)) * ((y * w) * x)
-- Conclusion: (x * x) * y = (y * (x * z)) * y
-- Original submission SHA-256: 5df07e3f8c941c85398f44c4916b2407670d1bc49494b3f88cb516e774433a90
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ x)) ◇ ((y ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (y ◇ (x ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q3 ◇ ((q2 ◇ q0) ◇ q1))) ◇ q1) = ((q2 ◇ q0) ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q2 ◇ (q3 ◇ ((q2 ◇ q0) ◇ q1))) ◇ t) ((h q1 q2 q0 q0).symm)).symm).trans ((h ((q2 ◇ q0) ◇ q1) q2 q3 (q0 ◇ q1)).symm)
  have apc1 : forall (q4 q5 q6:G), ((q6 ◇ q5) ◇ q5) = ((q6 ◇ q4) ◇ q5):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => q6 ◇ t) ((h q5 q6 q4 q4).symm))).symm).trans (apc0 q4 q5 q6 (q6 ◇ (q4 ◇ q5)))
  have apc5 : forall (q7 q8 q9 q10:G), (((q8 ◇ q10) ◇ q10) ◇ q10) = (((q8 ◇ q7) ◇ q9) ◇ q10):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ q10) ((apc1 q7 q10 q8).symm)).symm).trans (apc1 q9 q10 (q8 ◇ q7))
  have apc6 : forall (q11 q12 q13:G), (((q12 ◇ q13) ◇ q13) ◇ q13) = (q11 ◇ q13):=by
    intro q11 q12 q13
    exact (((congrArg (fun t => t ◇ q13) ((h q11 q12 q11 q11).symm)).symm).trans ((apc5 (q11 ◇ q11) q12 ((q12 ◇ q11) ◇ q11) q13).symm)).symm
  exact ((apc6 (x ◇ x) ((x ◇ x) ◇ y) y).symm).trans (apc6 (y ◇ (x ◇ z)) ((x ◇ x) ◇ y) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22769_to_60919 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22769_to_60919
