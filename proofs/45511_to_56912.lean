-- Equation45511 → Equation56912
-- Recorded verdict: true
-- Premise: x * y = y * (((z * z) * w) * x)
-- Conclusion: x * (y * y) = (z * (z * w)) * x
-- Original submission SHA-256: 74ae9edda1c8614da4577069da671966771bd707e21f2f17f66cac4f6ee31d96
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((z ◇ z) ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ (z ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ (q3 ◇ q3)) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 (q3 ◇ q3) q0 q0).symm))).symm).trans ((h q1 q2 q3 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q4 q0 q5 q6 q2 q3:G), (q2 ◇ (q0 ◇ ((q3 ◇ q3) ◇ q6))) = ((((q5 ◇ q5) ◇ q4) ◇ q0) ◇ q2):=by
    intro q4 q0 q5 q6 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 ((q3 ◇ q3) ◇ q6) q5 q4).symm)).symm).trans ((h (((q5 ◇ q5) ◇ q4) ◇ q0) q2 q3 q6).symm)
  have apc2 : forall (q7 q8 q9 q10 q11 q12 q13:G), ((((q9 ◇ q9) ◇ q7) ◇ q8) ◇ q10) = (q8 ◇ q10):=by
    intro q7 q8 q9 q10 q11 q12 q13
    exact (((apc0 ((q11 ◇ q11) ◇ q12) q8 q10 q13).symm).trans (((congrArg (fun t => q10 ◇ t) (apc1 q12 (q13 ◇ q13) q11 q12 q8 q12)).symm).trans (apc1 q7 q8 q9 ((q12 ◇ q12) ◇ q12) q10 q13))).symm
  have apc3 : forall (q14 q15 q16:G), (q16 ◇ (q14 ◇ q15)) = (q15 ◇ q16):=by
    intro q14 q15 q16
    exact ((congrArg (fun t => q16 ◇ t) (apc2 (q14 ◇ q14) q14 q14 q15 q14 q14 q14)).symm).trans ((h q15 q16 (q14 ◇ q14) q14).symm)
  have apc4 : forall (q17 q18 q19 q20 q21:G), (q18 ◇ q19) = (q17 ◇ q19):=by
    intro q17 q18 q19 q20 q21
    exact ((apc3 q17 q18 q19).symm).trans ((((congrArg (fun t => q19 ◇ t) ((h q17 q18 q20 q21).symm)).symm).trans (apc3 q18 (((q20 ◇ q20) ◇ q21) ◇ q17) q19)).trans (apc2 q21 q17 q20 q19 ((((q20 ◇ q20) ◇ q21) ◇ q17) ◇ q19) ((((q20 ◇ q20) ◇ q21) ◇ q17) ◇ q19) ((((q20 ◇ q20) ◇ q21) ◇ q17) ◇ q19)))
  have apc5 : forall (q22 q23 q24 q25 q26:G), (q23 ◇ q22) = (q22 ◇ q23):=by
    intro q22 q23 q24 q25 q26
    exact ((apc3 ((q24 ◇ q24) ◇ q25) q23 q22).symm).trans ((((apc3 q26 q22 (((q24 ◇ q24) ◇ q25) ◇ q23)).symm).trans (apc2 q25 q23 q24 (q26 ◇ q22) q26 q26 q26)).trans (apc3 q26 q22 q23))
  have apc7 : forall (q27 q28 q29:G), (q28 ◇ q29) = (q27 ◇ q28):=by
    intro q27 q28 q29
    exact (((apc4 q27 q29 q28 q27 q27).symm).trans (apc5 q28 q29 q27 q27 q27)).symm
  exact (apc7 x x (y ◇ y)).trans (apc7 (z ◇ (z ◇ w)) x x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45511_to_56912 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45511_to_56912
