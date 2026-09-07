-- Equation52647 → Equation52050
-- Recorded verdict: true
-- Premise: x * y = ((z * (y * x)) * w) * x
-- Conclusion: x * y = ((z * w) * (u * v)) * u
-- Original submission SHA-256: 0947a5787fcae8b3267141f06116e65bb07888354f5a2b19465d8d6789368250
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (y ◇ x)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ (u ◇ v)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h q1 q0 q0 (q3 ◇ q2)).symm)).symm).trans ((h q2 q3 (q0 ◇ (q0 ◇ q1)) q1).symm)
  have apc1 : forall (q0 q2 q3 q1:G), (q2 ◇ q3) = (q2 ◇ q0):=by
    intro q0 q2 q3 q1
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q1 q2 q0)
  have apc3 : forall (q4 q5 q6 q7 q8:G), ((q6 ◇ q5) ◇ q4) = (q7 ◇ q8):=by
    intro q4 q5 q6 q7 q8
    exact ((apc1 q4 (q6 ◇ q5) q7 q4).symm).trans (apc0 q5 q6 q7 q8)
  have apc6 : forall (q4 q7 q8 q5 q6:G), (q7 ◇ q8) = (q4 ◇ q4):=by
    intro q4 q7 q8 q5 q6
    exact ((apc3 q4 q5 q6 q7 q8).symm).trans (apc3 q4 q5 q6 q4 q4)
  exact (apc6 (x ◇ y) x y (x ◇ y) (x ◇ y)).trans ((apc6 (x ◇ y) ((z ◇ w) ◇ (u ◇ v)) u (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52647_to_52050 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52647_to_52050
