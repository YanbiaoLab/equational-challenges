-- Equation51481 → Equation3335
-- Recorded verdict: true
-- Premise: x * y = ((x * z) * (y * z)) * w
-- Conclusion: x * y = x * (z * (z * z))
-- Original submission SHA-256: 145e39edf8d0706b755f65da6c3a4014a96e3bcc03649cf0e3a4cacf95bb411c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ z) ◇ (y ◇ z)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (z ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q2) ◇ q4) = ((q0 ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 q2 (q4 ◇ (q1 ◇ q2))).symm)).symm).trans ((h (q0 ◇ q2) q4 (q1 ◇ q2) q3).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9:G), (((q7 ◇ q9) ◇ q5) ◇ q6) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9
    exact ((apc0 (q7 ◇ q9) q5 (q8 ◇ q9) q6 q5).symm).trans ((h q7 q8 q9 q5).symm)
  have apc2 : forall (q5 q6 q7 q8 q9:G), (q7 ◇ q8) = (q7 ◇ q5):=by
    intro q5 q6 q7 q8 q9
    exact ((apc1 q5 q6 q7 q8 q9).symm).trans (apc1 q5 q6 q7 q5 q9)
  exact (apc2 (x ◇ y) (x ◇ y) x y (x ◇ y)).trans ((apc2 (x ◇ y) (x ◇ y) x (z ◇ (z ◇ z)) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51481_to_3335 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51481_to_3335
