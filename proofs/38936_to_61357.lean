-- Equation38936 → Equation61357
-- Recorded verdict: true
-- Premise: x = (((x * x) * (y * z)) * x) * w
-- Conclusion: (x * y) * z = (x * (y * w)) * x
-- Original submission SHA-256: 4c8c1bec1209a0b2f8d0c5fe2486db0b54249af8f54baa306a46b357f10f220f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ x) ◇ (y ◇ z)) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (x ◇ (y ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q1 ◇ q2)) = ((q1 ◇ q2) ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q0) ((h (q1 ◇ q2) (q1 ◇ q2) (q1 ◇ q2) ((q1 ◇ q2) ◇ (q1 ◇ q2))).symm)).symm).trans ((h ((q1 ◇ q2) ◇ (q1 ◇ q2)) q1 q2 q0).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ q1) = ((q1 ◇ q2) ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q0 q1 q2).symm).trans (apc0 q1 q1 q2)).symm
  have apc2 : forall (q3 q4 q5 q6:G), ((q5 ◇ q6) ◇ q4) = ((q5 ◇ q6) ◇ q3):=by
    intro q3 q4 q5 q6
    exact (((apc0 q3 q5 q6).symm).trans (apc0 q4 q5 q6)).symm
  have apc3 : forall (q7 q0 q8:G), ((((q8 ◇ q8) ◇ q7) ◇ q8) ◇ q0) = q8:=by
    intro q7 q0 q8
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q8) (congrArg (fun t => (q8 ◇ q8) ◇ t) ((h q7 q7 q7 q7).symm)))).symm).trans ((h q8 (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ q7) q7 q0).symm)
  have apc4 : forall (q9 q10:G), (q9 ◇ q10) = (q9 ◇ q9):=by
    intro q9 q10
    exact (((congrArg (fun t => q9 ◇ t) (apc3 q9 q9 q9)).symm).trans ((((congrArg (fun t => t ◇ ((((q9 ◇ q9) ◇ q9) ◇ q9) ◇ q9)) (apc3 q9 q9 q9)).symm).trans (apc0 q10 (((q9 ◇ q9) ◇ q9) ◇ q9) q9)).trans (congrArg (fun t => t ◇ q10) (apc3 q9 q9 q9)))).symm
  have apc8 : forall (q11 q12 q13 q14 q15:G), (((q15 ◇ q12) ◇ q15) ◇ q13) = (((q15 ◇ q12) ◇ q11) ◇ q14):=by
    intro q11 q12 q13 q14 q15
    exact (((congrArg (fun t => t ◇ q14) (apc1 q11 q15 q12)).symm).trans (apc2 q13 q14 (q15 ◇ q12) q15)).symm
  have apc10 : forall (q16 q17 q18 q19:G), ((((q19 ◇ q19) ◇ q17) ◇ q16) ◇ q18) = q19:=by
    intro q16 q17 q18 q19
    exact ((congrArg (fun t => t ◇ q18) (apc2 q16 q19 (q19 ◇ q19) q17)).symm).trans (apc3 q17 q18 q19)
  have apc14 : forall (q20 q21 q22 q23 q24:G), (((q24 ◇ q24) ◇ q24) ◇ q22) = (((q24 ◇ q21) ◇ q20) ◇ q23):=by
    intro q20 q21 q22 q23 q24
    exact ((congrArg (fun t => t ◇ q22) (congrArg (fun t => t ◇ q24) (apc4 q24 q21))).symm).trans (apc8 q20 q21 q22 q23 q24)
  have apc15 : forall (q25 q26 q27 q28:G), ((q27 ◇ q27) ◇ q28) = ((q27 ◇ q26) ◇ q25):=by
    intro q25 q26 q27 q28
    exact (((congrArg (fun t => t ◇ q28) (congrArg (fun t => t ◇ q25) (apc10 q25 q27 q25 q27))).trans (congrArg (fun t => t ◇ q28) (apc4 q27 q25))).symm).trans (((congrArg (fun t => t ◇ q28) (congrArg (fun t => t ◇ q25) (congrArg (fun t => t ◇ q25) ((apc14 q25 q26 q25 ((q27 ◇ q26) ◇ q25) q27).symm)))).symm).trans (apc10 q25 q25 q28 ((q27 ◇ q26) ◇ q25)))
  exact ((apc15 z y x ((x ◇ y) ◇ z)).symm).trans (apc15 x (y ◇ w) x ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38936_to_61357 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38936_to_61357
