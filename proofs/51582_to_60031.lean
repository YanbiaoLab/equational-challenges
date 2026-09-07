-- Equation51582 → Equation60031
-- Recorded verdict: true
-- Premise: x * y = ((y * y) * (y * y)) * z
-- Conclusion: (x * x) * y = (x * z) * (w * y)
-- Original submission SHA-256: 95834ba8a8861c9623a53076f2e6c0d0e4733f5b4fe44f9cbc6891c38f636077
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ y) ◇ (y ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (x ◇ z) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ q1)) = ((q0 ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1))).symm)).symm).trans ((h q2 (q1 ◇ q1) q3).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), ((q1 ◇ q1) ◇ q1) = ((q0 ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((apc0 q0 q1 q2 q3).symm).trans (apc0 q1 q1 q2 q1)).symm
  have apc2 : forall (q4 q5 q6 q7:G), ((q5 ◇ q6) ◇ q7) = ((q4 ◇ q4) ◇ q4):=by
    intro q4 q5 q6 q7
    exact ((apc1 q4 q4 q4 (q6 ◇ q6)).trans (apc0 q5 q6 (q4 ◇ q4) q7)).symm
  exact (apc2 ((x ◇ x) ◇ y) x x y).trans ((apc2 ((x ◇ x) ◇ y) x z (w ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51582_to_60031 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51582_to_60031
