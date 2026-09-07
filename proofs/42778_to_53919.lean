-- Equation42778 → Equation53919
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ ((y ◇ z) ◇ z))
-- Conclusion: x ◇ (x ◇ y) = y ◇ (z ◇ (x ◇ w))
-- Original submission SHA-256: e21b8af9252841d84ee8e378fa33c906cba37d684c8c30880c87aeadb4c3f440
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ ((y ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = y ◇ (z ◇ (x ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (x ◇ ((y ◇ z) ◇ z))) = (y ◇ (x ◇ ((y ◇ x) ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), (y ◇ (x ◇ ((y ◇ x) ◇ x))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ ((q2 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h (q2 ◇ ((q1 ◇ q0) ◇ q0)) q1 q0).symm)).symm).trans ((h q1 q2 ((q1 ◇ q0) ◇ q0)).symm)
  have apc3 : forall (q3 q4 q5:G), (q5 ◇ (((q4 ◇ ((q5 ◇ q3) ◇ q3)) ◇ q5) ◇ q4)) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => t ◇ q4) ((h (q4 ◇ ((q5 ◇ q3) ◇ q3)) q5 q3).symm))).symm).trans (apc2 ((q5 ◇ q3) ◇ q3) q4 q5)
  have apc8 : forall (q6 q7 q8:G), (q8 ◇ ((((q8 ◇ ((q7 ◇ q6) ◇ q6)) ◇ q7) ◇ q8) ◇ q7)) = (q7 ◇ q8):=by
    intro q6 q7 q8
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q7) (cg (fun t => t ◇ q8) ((h (q8 ◇ ((q7 ◇ q6) ◇ q6)) q7 q6).symm)))).symm).trans (apc3 ((q7 ◇ q6) ◇ q6) q7 q8)
  have apc9 : forall (q9 q10:G), (((q10 ◇ ((q10 ◇ q9) ◇ q9)) ◇ q10) ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q9 q10
    exact (((cg (fun t => ((q10 ◇ ((q10 ◇ q9) ◇ q9)) ◇ q10) ◇ t) (apc8 q9 q10 q10)).symm).trans ((h q10 ((q10 ◇ ((q10 ◇ q9) ◇ q9)) ◇ q10) q10).symm)).trans (apc2 q9 q10 q10)
  have apc12 : forall (q11 q12 q13 q14:G), (q14 ◇ (q13 ◇ ((q12 ◇ q14) ◇ ((q14 ◇ ((q12 ◇ q11) ◇ q11)) ◇ q12)))) = (q13 ◇ q14):=by
    intro q11 q12 q13 q14
    exact ((cg (fun t => q14 ◇ t) (cg (fun t => q13 ◇ t) (cg (fun t => t ◇ ((q14 ◇ ((q12 ◇ q11) ◇ q11)) ◇ q12)) (apc2 q11 q12 q14)))).symm).trans ((h q13 q14 ((q14 ◇ ((q12 ◇ q11) ◇ q11)) ◇ q12)).symm)
  have apc13 : forall (q15 q16:G), ((q15 ◇ q15) ◇ (q16 ◇ (q15 ◇ q15))) = (q16 ◇ (q15 ◇ q15)):=by
    intro q15 q16
    exact (((cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => q16 ◇ t) (apc2 q15 ((q15 ◇ ((q15 ◇ q15) ◇ q15)) ◇ q15) (q15 ◇ q15)))).trans (cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => q16 ◇ t) (apc9 q15 q15)))).symm).trans (((cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ (((q15 ◇ q15) ◇ ((((q15 ◇ ((q15 ◇ q15) ◇ q15)) ◇ q15) ◇ q15) ◇ q15)) ◇ ((q15 ◇ ((q15 ◇ q15) ◇ q15)) ◇ q15))) (apc9 q15 q15)))).symm).trans (apc12 q15 ((q15 ◇ ((q15 ◇ q15) ◇ q15)) ◇ q15) q16 (q15 ◇ q15)))
  have apc14 : forall (q17:G), ((q17 ◇ q17) ◇ (q17 ◇ q17)) = (q17 ◇ q17):=by
    intro q17
    exact (((cg (fun t => (q17 ◇ q17) ◇ t) (apc9 q17 q17)).symm).trans (apc13 q17 ((q17 ◇ ((q17 ◇ q17) ◇ q17)) ◇ q17))).trans (apc9 q17 q17)
  have apc15 : forall (q18 q19:G), (q19 ◇ ((q19 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18))) = ((q18 ◇ q18) ◇ q19):=by
    intro q18 q19
    exact ((cg (fun t => q19 ◇ t) (apc13 q18 (q19 ◇ (q18 ◇ q18)))).symm).trans ((h (q18 ◇ q18) q19 (q18 ◇ q18)).symm)
  have apc16 : forall (q20 q21:G), (q21 ◇ ((q20 ◇ q20) ◇ q21)) = (q21 ◇ q21):=by
    intro q20 q21
    exact ((cg (fun t => q21 ◇ t) (apc15 q20 q21)).symm).trans ((h q21 q21 (q20 ◇ q20)).symm)
  have apc17 : forall (q22:G), (q22 ◇ (q22 ◇ q22)) = (q22 ◇ q22):=by
    intro q22
    exact ((cg (fun t => q22 ◇ t) (apc16 q22 q22)).symm).trans ((h q22 q22 q22).symm)
  have apc19 : forall (q23 q24:G), ((q23 ◇ q23) ◇ (q24 ◇ q24)) = (q24 ◇ q24):=by
    intro q23 q24
    exact (((apc14 q24).symm).trans (((apc16 q23 (q24 ◇ q24)).symm).trans (apc13 q24 (q23 ◇ q23)))).symm
  have apc20 : forall (q25 q26:G), (q26 ◇ q26) = (q25 ◇ q25):=by
    intro q25 q26
    exact ((((cg (fun t => (q25 ◇ q25) ◇ t) (cg (fun t => (q26 ◇ q26) ◇ t) (apc19 q26 q26))).trans (cg (fun t => (q25 ◇ q25) ◇ t) (apc19 q26 q26))).trans (apc19 q25 q26)).symm).trans ((((cg (fun t => (q25 ◇ q25) ◇ t) (cg (fun t => (q26 ◇ q26) ◇ t) (cg (fun t => t ◇ (q26 ◇ q26)) (apc19 q25 q26)))).symm).trans (apc1 (q26 ◇ q26) (q25 ◇ q25) q25)).trans (apc19 q26 q25))
  have apc21 : forall (q27 q28:G), (q28 ◇ (q27 ◇ q27)) = (q28 ◇ q28):=by
    intro q27 q28
    exact ((cg (fun t => q28 ◇ t) (apc20 q27 q28)).symm).trans (apc17 q28)
  have apc22 : forall (q29 q30:G), (q30 ◇ q30) = (q29 ◇ q30):=by
    intro q29 q30
    exact (((((cg (fun t => q30 ◇ t) (cg (fun t => q29 ◇ t) (cg (fun t => t ◇ (q30 ◇ (q29 ◇ q29))) (apc21 q29 q30)))).trans (cg (fun t => q30 ◇ t) (cg (fun t => q29 ◇ t) (cg (fun t => (q30 ◇ q30) ◇ t) (apc21 q29 q30))))).trans (cg (fun t => q30 ◇ t) (apc21 (q30 ◇ q30) q29))).trans (apc21 q29 q30)).symm).trans (((cg (fun t => q30 ◇ t) (cg (fun t => q29 ◇ t) (apc21 q29 (q30 ◇ (q29 ◇ q29))))).symm).trans ((h q29 q30 (q29 ◇ q29)).symm))
  have apc23 : forall (q31 q32 q33:G), (q32 ◇ q32) = (q31 ◇ q33):=by
    intro q31 q32 q33
    exact (((apc22 q31 q33).symm).trans (apc20 q32 q33)).symm
  exact ((apc23 x (x ◇ (x ◇ y)) (x ◇ y)).symm).trans (apc23 y (x ◇ (x ◇ y)) (z ◇ (x ◇ w)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42778_to_53919 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42778_to_53919
