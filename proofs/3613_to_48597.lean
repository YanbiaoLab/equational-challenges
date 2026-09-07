-- Equation3613 → Equation48597
-- Recorded verdict: true
-- Premise: x * y = z * ((y * w) * z)
-- Conclusion: x * x = ((y * x) * x) * (x * x)
-- Original submission SHA-256: 886bde4f623b2c3672eb1401ae0e3c7c0fef5a468ecd63873c78d1f23b71a265
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((y ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((y ◇ x) ◇ x) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q2 ◇ q0) ◇ (q5 ◇ q3)) ◇ (q1 ◇ q2)) = (q4 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => ((q2 ◇ q0) ◇ (q5 ◇ q3)) ◇ t) ((h q1 q2 (q5 ◇ q3) q0).symm)).symm).trans ((h q4 q5 ((q2 ◇ q0) ◇ (q5 ◇ q3)) q3).symm)
  have apc1 : forall (q6 q7 q8 q9 q10 q11 q12:G), (((q6 ◇ q7) ◇ (q12 ◇ q10)) ◇ (q8 ◇ q9)) = (q11 ◇ q12):=by
    intro q6 q7 q8 q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ (q8 ◇ q9)) (congrArg (fun t => t ◇ (q12 ◇ q10)) ((h q6 q7 q9 q6).symm))).symm).trans (apc0 ((q7 ◇ q6) ◇ q9) q8 q9 q10 q11 q12)
  have apc2 : forall (q13 q14 q15 q16 q17 q18:G), ((q13 ◇ q14) ◇ (q15 ◇ q16)) = (q17 ◇ q18):=by
    intro q13 q14 q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ (q15 ◇ q16)) (apc0 q13 q18 q13 q13 q13 q14)).symm).trans (apc1 (q13 ◇ q13) (q14 ◇ q13) q15 q16 q13 q17 q18)
  have apc6 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc7 : forall (q19 q20 q21 q22:G), ((q19 ◇ q20) ◇ (q19 ◇ q20)) = (q21 ◇ q22):=by
    intro q19 q20 q21 q22
    exact (apc6 (q19 ◇ q19) (q19 ◇ q20) q19 q19).trans (apc2 q19 q19 q19 q20 q21 q22)
  exact ((apc7 (x ◇ x) x x x).symm).trans (apc7 (x ◇ x) x ((y ◇ x) ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3613_to_48597 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3613_to_48597
