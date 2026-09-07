-- Equation48232 → Equation61806
-- Recorded verdict: true
-- Premise: x * y = (z * (x * w)) * (y * w)
-- Conclusion: (x * x) * y = ((y * y) * z) * y
-- Original submission SHA-256: 830f27ef4c52d165e14681f09e851ef60b65a1f6680282d3d7a29c24dbb06106
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ w)) ◇ (y ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = ((y ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q2) ◇ (q3 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q1)) ((h q0 q2 q0 q1).symm)).symm).trans ((h q2 q3 (q0 ◇ (q0 ◇ q1)) q1).symm)
  have apc1 : forall (q4 q5 q6 q7 q8 q9:G), ((q5 ◇ q6) ◇ q7) = ((q4 ◇ q5) ◇ q7):=by
    intro q4 q5 q6 q7 q8 q9
    exact ((apc0 q8 (q6 ◇ q9) (q5 ◇ q6) q7).symm).trans (((congrArg (fun t => t ◇ (q7 ◇ (q6 ◇ q9))) (congrArg (fun t => q8 ◇ t) (apc0 q4 q9 q5 q6))).symm).trans ((h (q4 ◇ q5) q7 q8 (q6 ◇ q9)).symm))
  exact (apc1 z x x y ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)).trans (apc1 (y ◇ y) z x y ((x ◇ x) ◇ y) ((x ◇ x) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48232_to_61806 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48232_to_61806
