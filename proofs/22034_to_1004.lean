-- Equation22034 → Equation1004
-- Recorded verdict: true
-- Premise: x = (y * (z * z)) * (y * (x * x))
-- Conclusion: x = y * ((z * w) * (z * x))
-- Original submission SHA-256: b9db9ed2a0da56051eb1380f518d5ea60f957bcc9c934ade76bdf49e84d1db79
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ z)) ◇ (y ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ w) ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q2 ◇ (q1 ◇ q1))) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q1 ◇ q1))) (congrArg (fun t => q2 ◇ t) ((h q0 q0 q0).symm))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q4 ◇ ((q5 ◇ q3) ◇ (q6 ◇ q6))) = q6:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ ((q5 ◇ q3) ◇ (q6 ◇ q6))) (apc0 q3 q4 q5)).symm).trans (apc0 (q5 ◇ (q4 ◇ q4)) q6 (q5 ◇ q3))
  have apc2 : forall (q7 q8 q9:G), (q8 ◇ (q7 ◇ (q9 ◇ q9))) = q9:=by
    intro q7 q8 q9
    exact ((congrArg (fun t => q8 ◇ t) (congrArg (fun t => t ◇ (q9 ◇ q9)) (apc1 q7 q7 q7 q7))).symm).trans (apc1 ((q7 ◇ q7) ◇ (q7 ◇ q7)) q8 q7 q9)
  have apc3 : forall (q10 q11 q12 q13 q14:G), (q13 ◇ ((q14 ◇ q12) ◇ q10)) = (q11 ◇ (q10 ◇ q10)):=by
    intro q10 q11 q12 q13 q14
    exact ((congrArg (fun t => q13 ◇ t) (congrArg (fun t => (q14 ◇ q12) ◇ t) (apc0 (q10 ◇ q10) q10 q11))).symm).trans (apc1 q12 q13 q14 (q11 ◇ (q10 ◇ q10)))
  have apc4 : forall (q15 q16 q17 q18 q19 q20 q21 q22:G), (q19 ◇ ((q20 ◇ q18) ◇ ((q17 ◇ q16) ◇ q15))) = q15:=by
    intro q15 q16 q17 q18 q19 q20 q21 q22
    exact (((apc2 q21 q22 q15).symm).trans (((congrArg (fun t => q22 ◇ t) (apc3 q15 q21 q16 ((q17 ◇ q16) ◇ q15) q17)).symm).trans ((apc3 ((q17 ◇ q16) ◇ q15) q22 q18 q19 q20).symm))).symm
  have apc5 : forall (q23 q24 q25 q26 q27:G), (q26 ◇ ((q27 ◇ q25) ◇ (q23 ◇ q24))) = q24:=by
    intro q23 q24 q25 q26 q27
    exact ((congrArg (fun t => q26 ◇ t) (congrArg (fun t => (q27 ◇ q25) ◇ t) (congrArg (fun t => t ◇ q24) (apc2 q23 q23 q23)))).symm).trans (apc4 q24 (q23 ◇ (q23 ◇ q23)) q23 q25 q26 q27 q23 q23)
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((z ◇ w) ◇ (z ◇ x))):=(apc5 z x w y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22034_to_1004 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22034_to_1004
