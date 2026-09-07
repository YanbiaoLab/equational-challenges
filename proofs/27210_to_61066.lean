-- Equation27210 → Equation61066
-- Recorded verdict: true
-- Premise: x = ((y * z) * (y * x)) * (z * x)
-- Conclusion: (x * y) * x = (y * (x * y)) * x
-- Original submission SHA-256: 0b475ff69ccfcebbb3615aecf9bd9dce5809a89f944c7aee76d98e5baa925714
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (y ◇ x)) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ x = (y ◇ (x ◇ y)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ z) ◇ (y ◇ x)) ◇ (z ◇ x)) = (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2:G), ((q1 ◇ (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q2)) ◇ ((q1 ◇ q1) ◇ q2)) = q2:=by
    intro q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q2)) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q2)) (apc1 q1))).symm).trans ((h q2 ((q1 ◇ q1) ◇ (q1 ◇ q1)) (q1 ◇ q1)).symm)
  have apc3 : forall (q3:G), ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) = (q3 ◇ q3):=by
    intro q3
    exact ((cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (cg (fun t => q3 ◇ t) (apc1 q3))).symm).trans (apc2 q3 (q3 ◇ q3))
  have apc5 : forall (q4 q5 q6 q7:G), ((q4 ◇ (((q5 ◇ q6) ◇ (q5 ◇ q4)) ◇ q7)) ◇ ((q6 ◇ q4) ◇ q7)) = q7:=by
    intro q4 q5 q6 q7
    exact ((cg (fun t => t ◇ ((q6 ◇ q4) ◇ q7)) (cg (fun t => t ◇ (((q5 ◇ q6) ◇ (q5 ◇ q4)) ◇ q7)) ((h q4 q5 q6).symm))).symm).trans ((h q7 ((q5 ◇ q6) ◇ (q5 ◇ q4)) (q6 ◇ q4)).symm)
  have apc6 : forall (q8 q9:G), ((q8 ◇ q8) ◇ ((q9 ◇ q8) ◇ (q9 ◇ q8))) = (q9 ◇ q8):=by
    intro q8 q9
    exact ((cg (fun t => t ◇ ((q9 ◇ q8) ◇ (q9 ◇ q8))) (cg (fun t => q8 ◇ t) ((h q8 q8 q9).symm))).symm).trans (apc5 q8 q8 q9 (q9 ◇ q8))
  have apc7 : forall (q10 q11 q12 q13:G), ((((q11 ◇ q10) ◇ q12) ◇ ((q11 ◇ q10) ◇ q12)) ◇ (q12 ◇ q12)) = q12:=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => (((q11 ◇ q10) ◇ q12) ◇ ((q11 ◇ q10) ◇ q12)) ◇ t) (cg (fun t => q12 ◇ t) (apc5 q10 q13 q11 q12))).symm).trans ((((cg (fun t => (((q11 ◇ q10) ◇ q12) ◇ ((q11 ◇ q10) ◇ q12)) ◇ t) (cg (fun t => t ◇ ((q10 ◇ (((q13 ◇ q11) ◇ (q13 ◇ q10)) ◇ q12)) ◇ ((q11 ◇ q10) ◇ q12))) (apc5 q10 q13 q11 q12))).symm).trans (apc6 ((q11 ◇ q10) ◇ q12) (q10 ◇ (((q13 ◇ q11) ◇ (q13 ◇ q10)) ◇ q12)))).trans (apc5 q10 q13 q11 q12))
  have apc8 : forall (q14 q15:G), (((q14 ◇ q15) ◇ (q14 ◇ q15)) ◇ (q15 ◇ q15)) = q15:=by
    intro q14 q15
    exact ((cg (fun t => t ◇ (q15 ◇ q15)) (cg (fun t => (q14 ◇ q15) ◇ t) (cg (fun t => t ◇ q15) (apc1 q14)))).symm).trans (((cg (fun t => t ◇ (q15 ◇ q15)) (cg (fun t => t ◇ ((((q14 ◇ q14) ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14)) ◇ q15)) (cg (fun t => t ◇ q15) (apc1 q14)))).symm).trans (apc7 (q14 ◇ q14) ((q14 ◇ q14) ◇ (q14 ◇ q14)) q15 q14))
  have apc10 : forall (q4 q5 q6 q16:G), (((((q5 ◇ q6) ◇ (q5 ◇ q4)) ◇ q16) ◇ q4) ◇ (q16 ◇ (q6 ◇ q4))) = (q6 ◇ q4):=by
    intro q4 q5 q6 q16
    exact ((cg (fun t => t ◇ (q16 ◇ (q6 ◇ q4))) (cg (fun t => (((q5 ◇ q6) ◇ (q5 ◇ q4)) ◇ q16) ◇ t) ((h q4 q5 q6).symm))).symm).trans ((h (q6 ◇ q4) ((q5 ◇ q6) ◇ (q5 ◇ q4)) q16).symm)
  have apc11 : forall (q17 q18:G), (((q17 ◇ q17) ◇ ((q17 ◇ q17) ◇ q18)) ◇ (((q17 ◇ q17) ◇ (q17 ◇ q17)) ◇ q18)) = q18:=by
    intro q17 q18
    exact ((cg (fun t => t ◇ (((q17 ◇ q17) ◇ (q17 ◇ q17)) ◇ q18)) (cg (fun t => t ◇ ((q17 ◇ q17) ◇ q18)) (apc3 q17))).symm).trans ((h q18 (q17 ◇ q17) ((q17 ◇ q17) ◇ (q17 ◇ q17))).symm)
  have apc12 : forall (q19:G), ((q19 ◇ q19) ◇ q19) = (q19 ◇ q19):=by
    intro q19
    exact ((cg (fun t => t ◇ q19) (apc6 q19 q19)).symm).trans (((cg (fun t => ((q19 ◇ q19) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) ◇ t) ((h q19 q19 q19).symm)).symm).trans (apc11 q19 (q19 ◇ q19)))
  have apc13 : forall (q20:G), ((q20 ◇ q20) ◇ (q20 ◇ q20)) = q20:=by
    intro q20
    exact ((apc12 (q20 ◇ q20)).symm).trans ((h q20 q20 q20).symm)
  have apc15 : forall (q4 q5 q6 q21:G), (((q21 ◇ ((q5 ◇ q6) ◇ (q5 ◇ q4))) ◇ (q21 ◇ (q6 ◇ q4))) ◇ q4) = (q6 ◇ q4):=by
    intro q4 q5 q6 q21
    exact ((cg (fun t => ((q21 ◇ ((q5 ◇ q6) ◇ (q5 ◇ q4))) ◇ (q21 ◇ (q6 ◇ q4))) ◇ t) ((h q4 q5 q6).symm)).symm).trans ((h (q6 ◇ q4) q21 ((q5 ◇ q6) ◇ (q5 ◇ q4))).symm)
  have apc16 : forall (q22 q23:G), (((q23 ◇ q22) ◇ q22) ◇ q22) = (q22 ◇ q22):=by
    intro q22 q23
    exact ((cg (fun t => ((q23 ◇ q22) ◇ q22) ◇ t) (apc8 q23 q22)).symm).trans (((cg (fun t => t ◇ (((q23 ◇ q22) ◇ (q23 ◇ q22)) ◇ (q22 ◇ q22))) (cg (fun t => t ◇ q22) (apc13 (q23 ◇ q22)))).symm).trans (apc10 q22 q23 q22 ((q23 ◇ q22) ◇ (q23 ◇ q22))))
  have apc17 : forall (q24 q25:G), ((q25 ◇ q24) ◇ (q25 ◇ q24)) = (q24 ◇ (q25 ◇ q24)):=by
    intro q24 q25
    exact (((cg (fun t => t ◇ (q25 ◇ q24)) ((h q24 q25 q25).symm)).symm).trans (apc16 (q25 ◇ q24) (q25 ◇ q25))).symm
  have apc18 : forall (q26 q27 q28 q29:G), (((q27 ◇ q26) ◇ q28) ◇ q28) = (q28 ◇ q28):=by
    intro q26 q27 q28 q29
    exact (((cg (fun t => q28 ◇ t) (apc5 q26 q29 q27 q28)).symm).trans ((((cg (fun t => t ◇ ((q26 ◇ (((q29 ◇ q27) ◇ (q29 ◇ q26)) ◇ q28)) ◇ ((q27 ◇ q26) ◇ q28))) (apc5 q26 q29 q27 q28)).symm).trans (apc17 ((q27 ◇ q26) ◇ q28) (q26 ◇ (((q29 ◇ q27) ◇ (q29 ◇ q26)) ◇ q28)))).trans (cg (fun t => ((q27 ◇ q26) ◇ q28) ◇ t) (apc5 q26 q29 q27 q28)))).symm
  have apc19 : forall (q30 q31:G), (q30 ◇ (q31 ◇ q30)) = q30:=by
    intro q30 q31
    exact ((apc17 q30 q31).symm).trans (((apc18 q31 q31 (q31 ◇ q30) q30).symm).trans ((h q30 q31 q31).symm))
  have apc20 : forall (q32 q33 q34:G), (q33 ◇ q32) = (q32 ◇ q32):=by
    intro q32 q33 q34
    exact (((apc18 ((q34 ◇ q33) ◇ (q34 ◇ q32)) q32 q32 (((q32 ◇ ((q34 ◇ q33) ◇ (q34 ◇ q32))) ◇ q32) ◇ q32)).symm).trans (((cg (fun t => t ◇ q32) (cg (fun t => (q32 ◇ ((q34 ◇ q33) ◇ (q34 ◇ q32))) ◇ t) (apc19 q32 q33))).symm).trans (apc15 q32 q34 q33 q32))).symm
  exact (apc20 x (x ◇ y) ((x ◇ y) ◇ x)).trans ((apc20 x (y ◇ (x ◇ y)) ((x ◇ y) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27210_to_61066 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27210_to_61066
