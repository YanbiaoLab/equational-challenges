-- Equation43708 → Equation54446
-- Recorded verdict: true
-- Premise: x * y = y * ((y * z) * (w * z))
-- Conclusion: x * (y * z) = y * (w * (y * y))
-- Original submission SHA-256: 35347bce8304463d4882818899d29f0f71b89d22be75adc42e75e67aca666c9c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((y ◇ z) ◇ (w ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = y ◇ (w ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q1 ◇ (q0 ◇ (q1 ◇ q3))) = (q2 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q1 ◇ t) (apc0 q0 (q1 ◇ q3) q0 q0)).symm).trans ((h q2 q1 q3 q1).symm)
  have apc12 : forall (q4 q5 q6 q7:G), (q6 ◇ (q4 ◇ q5)) = (q7 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q6 ◇ t) (apc1 q6 q5 q4 q4)).symm).trans (apc1 q5 q6 q7 (q5 ◇ q4))
  have apc13 : forall (q8 q9 q10 q11 q12:G), (q12 ◇ (q10 ◇ q11)) = (q12 ◇ (q8 ◇ q9)):=by
    intro q8 q9 q10 q11 q12
    exact ((apc12 q8 q9 q12 q8).trans ((apc12 q10 q11 q12 q8).symm)).symm
  have apc14 : forall (q13 q14 q15 q16:G), (q16 ◇ (q13 ◇ q14)) = (q15 ◇ (q13 ◇ q14)):=by
    intro q13 q14 q15 q16
    exact (((apc12 q13 q14 (q13 ◇ q14) q15).symm).trans (apc0 q16 (q13 ◇ q14) q13 q13)).symm
  have apc15 : forall (q8 q9 q10 q11 q12:G), (q12 ◇ (q10 ◇ q10)) = (q12 ◇ (q8 ◇ q9)):=by
    intro q8 q9 q10 q11 q12
    exact (((apc13 q8 q9 q10 q11 q12).symm).trans (apc13 q10 q10 q10 q11 q12)).symm
  have apc23 : forall (q17 q18 q19 q20 q21:G), (q21 ◇ (q17 ◇ q18)) = (q20 ◇ (q19 ◇ q19)):=by
    intro q17 q18 q19 q20 q21
    exact ((apc15 q17 q18 q19 q17 q21).symm).trans (apc14 q19 q19 q20 q21)
  exact (apc23 y z (x ◇ (y ◇ z)) (y ◇ (w ◇ (y ◇ y))) x).trans ((apc23 w (y ◇ y) (x ◇ (y ◇ z)) (y ◇ (w ◇ (y ◇ y))) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43708_to_54446 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43708_to_54446
