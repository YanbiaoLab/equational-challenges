-- Equation51948 → Equation53142
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * (y * z)) * x
-- Conclusion: x * y = (((x * x) * x) * z) * w
-- Original submission SHA-256: c238338ca0a9b65cb0dc1c3b5ab2aa8c84c89b86a432463ee6a4cffa98b66076
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ (y ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((x ◇ x) ◇ x) ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ (q2 ◇ q0)) ◇ q1) ◇ q3) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q3) ((h (q4 ◇ (q2 ◇ q0)) q1 q2 q0).symm)).symm).trans ((h q3 q4 (q2 ◇ q0) (q1 ◇ q2)).symm)
  have apc1 : forall (q5 q6 q7:G), (q5 ◇ q7) = (q5 ◇ q6):=by
    intro q5 q6 q7
    exact ((apc0 q5 (q6 ◇ q7) q5 q5 q7).symm).trans ((h q5 q6 q7 (q5 ◇ q5)).symm)
  have apc2 : forall (q8 q9 q10 q11 q12:G), (((q12 ◇ q9) ◇ q8) ◇ q10) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q10) (apc1 (q12 ◇ q9) q8 (q11 ◇ q12))).symm).trans ((h q10 q11 q12 q9).symm)
  have apc3 : forall (q13 q14 q15 q16:G), (((q16 ◇ q13) ◇ q14) ◇ q15) = (q15 ◇ q16):=by
    intro q13 q14 q15 q16
    exact ((congrArg (fun t => t ◇ q15) (congrArg (fun t => t ◇ q14) (apc1 q16 q13 (q13 ◇ q13)))).symm).trans (apc0 q13 q14 q13 q15 q16)
  have apc4 : forall (q17 q18 q19 q20:G), ((q18 ◇ q17) ◇ q19) = (q19 ◇ q20):=by
    intro q17 q18 q19 q20
    exact ((congrArg (fun t => t ◇ q19) (apc2 q17 q17 q18 q17 q17)).symm).trans (apc2 q18 q17 q19 q20 (q17 ◇ q17))
  have apc5 : forall (x y z w:G), (x ◇ z) = (x ◇ x):=by
    intro x y z w
    exact ((apc3 w (y ◇ z) x z).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (apc3 x (y ◇ x) x x))
  have apc8 : forall (x y z w q17 q18 q19 q20:G), ((q18 ◇ q17) ◇ q19) = (q19 ◇ q19):=by
    intro x y z w q17 q18 q19 q20
    exact (apc4 q17 q18 q19 q20).trans (apc5 q19 (q19 ◇ q20) q20 (q19 ◇ q20))
  have apc9 : forall (q21 q22 q23 q24 q25 q26:G), (q23 ◇ q21) = (q22 ◇ q22):=by
    intro q21 q22 q23 q24 q25 q26
    exact (((apc2 q24 q25 q23 q21 q26).symm).trans (apc1 ((q26 ◇ q25) ◇ q24) q22 q23)).trans ((congrArg (fun t => t ◇ q22) (apc8 ((q26 ◇ q25) ◇ q24) ((q26 ◇ q25) ◇ q24) ((q26 ◇ q25) ◇ q24) ((q26 ◇ q25) ◇ q24) q25 q26 q24 ((q26 ◇ q25) ◇ q24))).trans (apc8 ((q24 ◇ q24) ◇ q22) ((q24 ◇ q24) ◇ q22) ((q24 ◇ q24) ◇ q22) ((q24 ◇ q24) ◇ q22) q24 q24 q22 ((q24 ◇ q24) ◇ q22)))
  exact (apc9 y (x ◇ y) x (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc9 w (x ◇ y) (((x ◇ x) ◇ x) ◇ z) (x ◇ y) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51948_to_53142 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51948_to_53142
