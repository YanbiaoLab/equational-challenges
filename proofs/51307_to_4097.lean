-- Equation51307 → Equation4097
-- Recorded verdict: true
-- Premise: x * x = ((y * z) * (x * y)) * y
-- Conclusion: x * x = ((y * y) * z) * y
-- Original submission SHA-256: 51133a4153988ca119f0f6aa75547b6a431d563cc4c78a7270a7ef7a1d783fef
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ z) ◇ (x ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (((y ◇ z) ◇ (x ◇ y)) ◇ y) = (((x ◇ x) ◇ (x ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (((x ◇ x) ◇ (x ◇ x)) ◇ x) = (x ◇ x):=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ (q0 ◇ q2)) ◇ ((q2 ◇ q1) ◇ (q0 ◇ q2))) = (((q2 ◇ q3) ◇ (q0 ◇ q0)) ◇ q2):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q2) (congrArg (fun t => (q2 ◇ q3) ◇ t) ((h q0 q2 q1).symm))).symm).trans ((h ((q2 ◇ q1) ◇ (q0 ◇ q2)) q2 q3).symm)).symm
  have apc3 : forall (q0 q1 q2 q3:G), (((q2 ◇ q3) ◇ (q0 ◇ q0)) ◇ q2) = (((q2 ◇ q0) ◇ (q0 ◇ q0)) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((apc2 q0 q0 q2 q3).symm).trans (apc2 q0 q0 q2 q0)
  have apc4 : forall (q4 q5:G), (((q5 ◇ q4) ◇ (q5 ◇ q5)) ◇ ((q5 ◇ q4) ◇ (q5 ◇ q5))) = (q5 ◇ q5):=by
    intro q4 q5
    exact (apc2 q5 q4 q5 q4).trans ((h q5 q5 q4).symm)
  have apc5 : forall (q6 q7:G), (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q7))) = (q7 ◇ q7):=by
    intro q6 q7
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q6) ◇ (q7 ◇ q7))) (congrArg (fun t => (q7 ◇ q7) ◇ t) (apc4 q6 q7))).symm).trans ((((congrArg (fun t => t ◇ ((q7 ◇ q6) ◇ (q7 ◇ q7))) (congrArg (fun t => t ◇ (((q7 ◇ q6) ◇ (q7 ◇ q7)) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q7)))) (apc4 q6 q7))).symm).trans (apc1 ((q7 ◇ q6) ◇ (q7 ◇ q7)) q6 q6)).trans (apc4 q6 q7))
  have apc6 : forall (q8 q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = ((q9 ◇ q8) ◇ (q9 ◇ q8)):=by
    intro q8 q9
    exact ((congrArg (fun t => t ◇ (q9 ◇ q9)) (apc5 q8 q9)).symm).trans ((h (q9 ◇ q8) (q9 ◇ q9) (q9 ◇ q9)).symm)
  have apc7 : forall (q10 q11 q12:G), ((q12 ◇ q11) ◇ (q12 ◇ q11)) = ((q12 ◇ q10) ◇ (q12 ◇ q10)):=by
    intro q10 q11 q12
    exact (((apc6 q10 q12).symm).trans (apc6 q11 q12)).symm
  have apc8 : forall (q13 q14:G), (((q14 ◇ q13) ◇ (q14 ◇ q13)) ◇ q14) = (q14 ◇ q14):=by
    intro q13 q14
    exact ((congrArg (fun t => t ◇ q14) (apc6 q13 q14)).symm).trans ((h q14 q14 q14).symm)
  have apc9 : forall (q15 q16:G), ((q16 ◇ q16) ◇ (q16 ◇ q15)) = ((q16 ◇ q15) ◇ (q16 ◇ q15)):=by
    intro q15 q16
    exact ((congrArg (fun t => t ◇ (q16 ◇ q15)) (apc4 q15 q16)).symm).trans (apc8 (q16 ◇ q16) (q16 ◇ q15))
  have apc11 : forall (q17 q18 q19:G), (((q19 ◇ q18) ◇ q17) ◇ ((q19 ◇ q18) ◇ q17)) = (q19 ◇ q19):=by
    intro q17 q18 q19
    exact ((apc7 q17 (q19 ◇ q19) (q19 ◇ q18)).symm).trans (apc4 q18 q19)
  have apc12 : forall (q20 q21 q22 q23:G), ((q22 ◇ q22) ◇ (((q22 ◇ q21) ◇ q20) ◇ q23)) = ((q22 ◇ q21) ◇ (q22 ◇ q21)):=by
    intro q20 q21 q22 q23
    exact (((congrArg (fun t => t ◇ (((q22 ◇ q21) ◇ q20) ◇ q23)) (apc11 q20 q21 q22)).symm).trans (apc9 q23 ((q22 ◇ q21) ◇ q20))).trans (apc11 q23 q20 (q22 ◇ q21))
  have apc13 : forall (q24 q25 q26:G), ((q26 ◇ q26) ◇ (q24 ◇ q24)) = ((q26 ◇ q25) ◇ (q26 ◇ q25)):=by
    intro q24 q25 q26
    exact ((congrArg (fun t => (q26 ◇ q26) ◇ t) ((h q24 q26 q25).symm)).symm).trans (apc12 (q24 ◇ q26) q25 q26 q26)
  have apc16 : forall (q27 q28:G), (((q28 ◇ q27) ◇ (q27 ◇ q27)) ◇ q28) = (q28 ◇ q28):=by
    intro q27 q28
    exact ((apc3 q27 (((q28 ◇ q28) ◇ (q27 ◇ q27)) ◇ q28) q28 q28).symm).trans (((congrArg (fun t => t ◇ q28) ((apc13 q27 q28 q28).symm)).symm).trans ((h q28 q28 q28).symm))
  have apc17 : forall (q0 q1 q2 q3 q27 q28:G), (((q2 ◇ q3) ◇ (q0 ◇ q0)) ◇ q2) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3 q27 q28
    exact (apc3 q0 q0 q2 q3).trans (apc16 q0 q2)
  have apc18 : forall (q29 q30 q31:G), ((q29 ◇ q29) ◇ ((q31 ◇ q31) ◇ q30)) = (q31 ◇ q31):=by
    intro q29 q30 q31
    exact (((congrArg (fun t => t ◇ ((q31 ◇ q31) ◇ q30)) ((h q29 (q31 ◇ q31) q30).symm)).symm).trans (apc17 q31 q29 ((q31 ◇ q31) ◇ q30) (q29 ◇ (q31 ◇ q31)) q29 q29)).trans (apc11 q30 q31 q31)
  have apc19 : forall (q32 q33:G), ((q32 ◇ q32) ◇ q33) = (q33 ◇ q33):=by
    intro q32 q33
    exact ((congrArg (fun t => t ◇ q33) (apc18 q33 (q32 ◇ q32) q32)).symm).trans (apc17 (q32 ◇ q32) q32 q33 q33 q32 q32)
  have apc20 : forall (q34 q35:G), (q35 ◇ q35) = (q34 ◇ q34):=by
    intro q34 q35
    exact ((apc19 (q34 ◇ q35) q35).symm).trans (((congrArg (fun t => t ◇ q35) (apc19 q35 (q34 ◇ q35))).symm).trans ((h q34 q35 q35).symm))
  exact (calc
    (x ◇ x) = (y ◇ y):=apc20 y x
    _ = ((z ◇ z) ◇ y):=(apc19 z y).symm
    _ = (((y ◇ y) ◇ z) ◇ y):=(congrArg (fun t => t ◇ y) (apc19 y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51307_to_4097 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51307_to_4097
