-- Equation49389 → Equation60005
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * u) * (x * u)
-- Conclusion: (x * x) * y = (x * x) * (z * y)
-- Original submission SHA-256: fdb67fbe9c08626ffb6fc5f1230f46ebd17814b3538a9d2af4b404927b02208d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ w) ◇ u) ◇ (x ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (x ◇ x) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ (q3 ◇ (q0 ◇ q2))) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ (q0 ◇ q2))) ((h q0 q1 q0 q0 q2).symm)).symm).trans ((h q3 q4 (q0 ◇ q0) q2 (q0 ◇ q2)).symm)
  have apc1 : forall (q5 q6 q7 q8 q9 q10:G), ((q8 ◇ q9) ◇ (q8 ◇ q7)) = ((q5 ◇ q6) ◇ q10):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((congrArg (fun t => (q8 ◇ q9) ◇ t) (apc0 q5 q6 q5 q8 q7)).symm).trans (apc0 q8 q9 (q5 ◇ q5) (q5 ◇ q6) q10)
  have apc2 : forall (q5 q6 q7 q8 q9 q10:G), ((q7 ◇ q7) ◇ q7) = ((q5 ◇ q6) ◇ q10):=by
    intro q5 q6 q7 q8 q9 q10
    exact (((apc1 q5 q6 q7 q8 q9 q10).symm).trans (apc1 q7 q7 q7 q8 q9 q7)).symm
  exact ((apc2 x x ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) y).symm).trans (apc2 x x ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) (z ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49389_to_60005 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49389_to_60005
