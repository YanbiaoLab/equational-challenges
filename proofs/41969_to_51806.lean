-- Equation41969 → Equation51806
-- Recorded verdict: true
-- Premise: x * y = y * (z * (x * (w * x)))
-- Conclusion: x * y = ((z * y) * (z * w)) * z
-- Original submission SHA-256: c357702e22eaa69467b2caaa382b9d929c1e829f879064d24cd6ff9bfd817b8c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ (x ◇ (w ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ (z ◇ w)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ q3)) = ((q0 ◇ q1) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q1 q3 (q0 ◇ q1) q0).symm)).symm).trans ((h (q0 ◇ q1) q2 q3 q1).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q4 ◇ q7) ◇ q6) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((apc0 q4 q7 q6 (q5 ◇ (q4 ◇ q5))).symm).trans ((h q5 q6 q7 q4).symm)
  have apc2 : forall (q4 q5 q6 q7:G), (q5 ◇ q6) = (q4 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((apc1 q4 q5 q6 q7).symm).trans (apc1 q4 q4 q6 q7)
  have apc3 : forall (q8 q9 q10 q11:G), (q10 ◇ (q9 ◇ q11)) = (q8 ◇ q10):=by
    intro q8 q9 q10 q11
    exact (((apc1 q8 q8 q10 q9).symm).trans ((apc0 q8 q9 q10 q11).symm)).symm
  have apc8 : forall (q12 q13 q14 q15 q16:G), (q15 ◇ (q13 ◇ q14)) = (q12 ◇ q16):=by
    intro q12 q13 q14 q15 q16
    exact (((apc3 q12 q13 q16 q14).symm).trans (apc2 q15 q16 (q13 ◇ q14) q12)).symm
  have apc10 : forall (q12 q13 q16 q14 q15:G), (q13 ◇ q13) = (q12 ◇ q16):=by
    intro q12 q13 q16 q14 q15
    exact (((apc8 q12 q13 q14 q15 q16).symm).trans (apc8 q13 q13 q14 q15 q13)).symm
  exact ((apc10 x (x ◇ y) y (x ◇ y) (x ◇ y)).symm).trans (apc10 ((z ◇ y) ◇ (z ◇ w)) (x ◇ y) z (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41969_to_51806 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41969_to_51806
