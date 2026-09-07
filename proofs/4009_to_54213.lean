-- Equation4009 → Equation54213
-- Recorded verdict: true
-- Premise: x * y = (z * (y * y)) * x
-- Conclusion: x * (y * y) = y * (y * (y * z))
-- Original submission SHA-256: 495c9397e400596174a82bc0ea15ec8770024e288d4239a06fc0c3e0d3af0765
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = y ◇ (y ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q0) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ q2) q0 q0).symm)).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc0 (q5 ◇ q5) q4 q3).symm).trans ((h q4 q5 (q3 ◇ q3)).symm)).symm
  have apc3 : forall (q6 q7 q8 q9:G), (q7 ◇ q8) = (q6 ◇ q8):=by
    intro q6 q7 q8 q9
    exact (((apc0 q9 q6 q8).symm).trans (((apc1 q6 ((q8 ◇ q8) ◇ q9) q7).symm).trans (apc0 q9 q7 q8))).symm
  have apc6 : forall (q10 q11 q12 q13:G), (q12 ◇ q11) = (q10 ◇ q13):=by
    intro q10 q11 q12 q13
    exact (((apc3 q10 q12 q13 q10).symm).trans (apc1 q11 q12 q13)).symm
  exact (apc6 (x ◇ (y ◇ y)) (y ◇ y) x (y ◇ (y ◇ (y ◇ z)))).trans ((apc6 (x ◇ (y ◇ y)) (y ◇ (y ◇ z)) y (y ◇ (y ◇ (y ◇ z)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4009_to_54213 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4009_to_54213
