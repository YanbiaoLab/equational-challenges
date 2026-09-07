-- Equation48262 → Equation50111
-- Recorded verdict: true
-- Premise: x * y = (z * (y * x)) * (w * x)
-- Conclusion: x * y = (z * (z * (y * w))) * y
-- Original submission SHA-256: c56128752f86a98a1ce41ad664a1b15705e04ae3b2e2ba4fa3daa5469e2f84ad
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (y ◇ x)) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (z ◇ (y ◇ w))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q1 ◇ q2)) ((h q2 q0 q0 q3).symm)).symm).trans ((h q2 q3 (q0 ◇ (q0 ◇ q2)) q1).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (q2 ◇ q3) = (q2 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q1 q2 q0)
  have apc2 : forall (q4 q5 q6 q7:G), ((q7 ◇ (q6 ◇ q5)) ◇ q4) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((apc1 q4 q4 (q7 ◇ (q6 ◇ q5)) (q4 ◇ q5)).symm).trans ((h q5 q6 q7 q4).symm)
  have apc3 : forall (q8 q9 q10 q11:G), ((q10 ◇ q9) ◇ q8) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((apc1 q8 q8 (q10 ◇ q9) (q8 ◇ q10)).symm).trans (apc0 q9 q8 q10 q11)
  have apc5 : forall (q12 q13 q14 q15 q16:G), ((q13 ◇ q14) ◇ q12) = (q13 ◇ q14):=by
    intro q12 q13 q14 q15 q16
    exact ((congrArg (fun t => t ◇ q12) (apc2 q15 q13 q14 q16)).symm).trans ((apc3 q12 q15 (q16 ◇ (q14 ◇ q13)) q12).trans (apc2 q12 q13 q14 q16))
  have apc6 : forall (q17 q18 q19 q20 q21:G), (q20 ◇ (q19 ◇ q17)) = (q18 ◇ q19):=by
    intro q17 q18 q19 q20 q21
    exact ((apc5 q21 q20 (q19 ◇ q17) ((q20 ◇ (q19 ◇ q17)) ◇ q21) ((q20 ◇ (q19 ◇ q17)) ◇ q21)).symm).trans (((congrArg (fun t => t ◇ q21) (congrArg (fun t => q20 ◇ t) (apc1 q17 q17 q19 q18))).symm).trans (apc2 q21 q18 q19 q20))
  exact ((apc6 (x ◇ y) x y ((z ◇ (z ◇ (y ◇ w))) ◇ y) (x ◇ y)).symm).trans (apc6 (x ◇ y) (z ◇ (z ◇ (y ◇ w))) y ((z ◇ (z ◇ (y ◇ w))) ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48262_to_50111 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48262_to_50111
