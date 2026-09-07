-- Equation42874 → Equation43889
-- Recorded verdict: true
-- Premise: x * y = y * (z * ((z * y) * z))
-- Conclusion: x * y = z * ((y * y) * (y * w))
-- Original submission SHA-256: b22525d0de79e270dc511b23c89394896edd1fe20cd16219284b8fc2a91c0624
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ ((z ◇ y) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((y ◇ y) ◇ (y ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ (q6 ◇ (q3 ◇ q6))) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q6 ◇ t) (apc0 q3 (q6 ◇ q5) q6))).symm).trans ((h q4 q5 q6).symm)
  have apc3 : forall (q7 q8 q9 q10 q11:G), (q11 ◇ (q8 ◇ (q7 ◇ q9))) = (q10 ◇ q11):=by
    intro q7 q8 q9 q10 q11
    exact ((congrArg (fun t => q11 ◇ t) (apc2 q7 q8 (q7 ◇ q9) q9)).symm).trans (apc2 q9 q10 q11 (q7 ◇ q9))
  have apc4 : forall (q12 q13 q14 q15:G), (q15 ◇ (q12 ◇ q13)) = (q14 ◇ q15):=by
    intro q12 q13 q14 q15
    exact ((congrArg (fun t => q15 ◇ t) (apc2 q12 q12 q13 q12)).symm).trans (apc3 q12 q13 (q12 ◇ q12) q14 q15)
  have apc6 : forall (q16 q17 q18 q19 q20:G), (q19 ◇ (q16 ◇ q17)) = (q18 ◇ q20):=by
    intro q16 q17 q18 q19 q20
    exact (((apc4 q16 q17 q18 q20).symm).trans (apc0 q19 q20 (q16 ◇ q17))).symm
  have apc8 : forall (q16 q18 q20 q17 q19:G), (q18 ◇ q20) = (q16 ◇ q16):=by
    intro q16 q18 q20 q17 q19
    exact ((apc6 q16 q17 q18 q19 q20).symm).trans (apc6 q16 q17 q16 q19 q16)
  exact (apc8 (x ◇ y) x y (x ◇ y) (x ◇ y)).trans ((apc8 (x ◇ y) z ((y ◇ y) ◇ (y ◇ w)) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42874_to_43889 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42874_to_43889
