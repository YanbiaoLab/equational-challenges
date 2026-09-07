-- Equation49131 → Equation54787
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * x) * (y * x)
-- Conclusion: x * (x * y) = y * ((y * y) * y)
-- Original submission SHA-256: dd4ef7f9b54c1230f125cd2a511a61c74f83267bc362f5d90b17b2218d6f9812
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ y) ◇ x) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = y ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q0 ◇ q1))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) ((h q1 q0 q0).symm)).symm).trans ((h (q0 ◇ q1) q1 (q0 ◇ q0)).symm)
  have apc1 : forall (x y z:G), (((z ◇ y) ◇ x) ◇ (y ◇ x)) = (((x ◇ y) ◇ x) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (x y z:G), (((x ◇ y) ◇ x) ◇ (y ◇ x)) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc1 x y x)).symm
  have apc3 : forall (q2 q0 q3:G), (((q2 ◇ q0) ◇ q3) ◇ ((q0 ◇ q2) ◇ q3)) = (q3 ◇ (q0 ◇ q2)):=by
    intro q2 q0 q3
    exact ((cg (fun t => t ◇ ((q0 ◇ q2) ◇ q3)) (cg (fun t => t ◇ q3) ((h q2 q0 q2).symm))).symm).trans ((h q3 (q0 ◇ q2) ((q2 ◇ q0) ◇ q2)).symm)
  have apc4 : forall (q4:G), ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4)) = (q4 ◇ (q4 ◇ q4)):=by
    intro q4
    exact (((apc3 q4 q4 q4).symm).trans (((cg (fun t => ((q4 ◇ q4) ◇ q4) ◇ t) (apc0 q4 q4)).symm).trans (apc0 q4 (q4 ◇ q4)))).symm
  have apc8 : forall (q5 q6:G), (((q5 ◇ q6) ◇ q6) ◇ (q5 ◇ (q6 ◇ (q5 ◇ q6)))) = ((q6 ◇ (q5 ◇ q6)) ◇ q5):=by
    intro q5 q6
    exact ((cg (fun t => t ◇ (q5 ◇ (q6 ◇ (q5 ◇ q6)))) (apc0 q5 q6)).symm).trans ((h (q6 ◇ (q5 ◇ q6)) q5 q6).symm)
  have apc13 : forall (q7:G), ((q7 ◇ (q7 ◇ q7)) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) = ((q7 ◇ q7) ◇ (q7 ◇ q7)):=by
    intro q7
    exact ((cg (fun t => t ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) (apc4 q7)).symm).trans ((h (q7 ◇ q7) (q7 ◇ q7) q7).symm)
  have apc15 : forall (q8:G), (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ (q8 ◇ (q8 ◇ q8))) = ((q8 ◇ q8) ◇ (q8 ◇ q8)):=by
    intro q8
    exact (((((((cg (fun t => (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ t) (cg (fun t => (q8 ◇ (q8 ◇ q8)) ◇ t) (cg (fun t => ((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ t) (apc13 q8)))).trans (cg (fun t => (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ t) (cg (fun t => (q8 ◇ (q8 ◇ q8)) ◇ t) (apc3 q8 q8 (q8 ◇ q8))))).trans (cg (fun t => (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ t) (apc13 q8))).trans (cg (fun t => t ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) (apc3 q8 q8 (q8 ◇ q8)))).trans (apc3 q8 q8 (q8 ◇ q8))).symm).trans ((((cg (fun t => t ◇ ((q8 ◇ (q8 ◇ q8)) ◇ (((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ ((q8 ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8)))))) (cg (fun t => t ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) (apc13 q8))).symm).trans (apc8 (q8 ◇ (q8 ◇ q8)) ((q8 ◇ q8) ◇ (q8 ◇ q8)))).trans ((cg (fun t => t ◇ (q8 ◇ (q8 ◇ q8))) (cg (fun t => ((q8 ◇ q8) ◇ (q8 ◇ q8)) ◇ t) (apc13 q8))).trans (cg (fun t => t ◇ (q8 ◇ (q8 ◇ q8))) (apc3 q8 q8 (q8 ◇ q8)))))).symm
  have apc16 : forall (q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = ((q9 ◇ q9) ◇ q9):=by
    intro q9
    exact ((apc15 q9).symm).trans ((h (q9 ◇ q9) q9 q9).symm)
  have apc17 : forall (q10:G), (q10 ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10
    exact (((cg (fun t => ((q10 ◇ q10) ◇ q10) ◇ t) (apc16 q10)).trans (apc3 q10 q10 q10)).symm).trans ((((cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc16 q10)).symm).trans (apc16 (q10 ◇ q10))).trans ((cg (fun t => t ◇ (q10 ◇ q10)) (apc16 q10)).trans (apc2 q10 q10 (((q10 ◇ q10) ◇ q10) ◇ (q10 ◇ q10)))))
  have apc18 : forall (q11:G), ((q11 ◇ q11) ◇ q11) = (q11 ◇ q11):=by
    intro q11
    exact ((((cg (fun t => t ◇ (q11 ◇ q11)) (apc16 q11)).trans (apc2 q11 q11 (((q11 ◇ q11) ◇ q11) ◇ (q11 ◇ q11)))).symm).trans ((((apc16 (q11 ◇ q11)).symm).trans (apc3 q11 q11 (q11 ◇ q11))).trans (apc16 q11))).symm
  have apc19 : forall (q10 q4:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = (q4 ◇ q4):=by
    intro q10 q4
    exact ((cg (fun t => t ◇ (q4 ◇ q4)) (apc17 q4)).symm).trans ((apc4 q4).trans (apc17 q4))
  have apc20 : forall (q12 q13:G), (((q13 ◇ q13) ◇ q12) ◇ (q13 ◇ q12)) = (q12 ◇ q13):=by
    intro q12 q13
    exact ((cg (fun t => t ◇ (q13 ◇ q12)) (cg (fun t => t ◇ q12) (apc18 q13))).symm).trans ((h q12 q13 (q13 ◇ q13)).symm)
  have apc22 : forall (q14 q15:G), (((q15 ◇ q14) ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q14 q15
    exact (((cg (fun t => ((q15 ◇ q14) ◇ (q14 ◇ q14)) ◇ t) (apc17 q14)).symm).trans ((h (q14 ◇ q14) q14 q15).symm)).trans (apc18 q14)
  have apc26 : forall (q16 q17:G), ((q16 ◇ q16) ◇ ((q17 ◇ q16) ◇ (q16 ◇ q16))) = (q16 ◇ q16):=by
    intro q16 q17
    exact (((((((cg (fun t => ((q16 ◇ q16) ◇ (q16 ◇ q16)) ◇ t) (cg (fun t => ((q17 ◇ q16) ◇ (q16 ◇ q16)) ◇ t) (cg (fun t => (q16 ◇ q16) ◇ t) (apc22 q16 q17)))).trans (cg (fun t => ((q16 ◇ q16) ◇ (q16 ◇ q16)) ◇ t) (cg (fun t => ((q17 ◇ q16) ◇ (q16 ◇ q16)) ◇ t) (apc19 ((q16 ◇ q16) ◇ (q16 ◇ q16)) q16)))).trans (cg (fun t => t ◇ (((q17 ◇ q16) ◇ (q16 ◇ q16)) ◇ (q16 ◇ q16))) (apc19 ((q16 ◇ q16) ◇ (q16 ◇ q16)) q16))).trans (cg (fun t => (q16 ◇ q16) ◇ t) (apc22 q16 q17))).trans (apc19 ((q16 ◇ q16) ◇ (q16 ◇ q16)) q16)).symm).trans ((((cg (fun t => t ◇ (((q17 ◇ q16) ◇ (q16 ◇ q16)) ◇ ((q16 ◇ q16) ◇ (((q17 ◇ q16) ◇ (q16 ◇ q16)) ◇ (q16 ◇ q16))))) (cg (fun t => t ◇ (q16 ◇ q16)) (apc22 q16 q17))).symm).trans (apc8 ((q17 ◇ q16) ◇ (q16 ◇ q16)) (q16 ◇ q16))).trans ((cg (fun t => t ◇ ((q17 ◇ q16) ◇ (q16 ◇ q16))) (cg (fun t => (q16 ◇ q16) ◇ t) (apc22 q16 q17))).trans (cg (fun t => t ◇ ((q17 ◇ q16) ◇ (q16 ◇ q16))) (apc19 ((q16 ◇ q16) ◇ (q16 ◇ q16)) q16))))).symm
  have apc27 : forall (q18 q19:G), ((q18 ◇ q18) ◇ (q19 ◇ q18)) = (q18 ◇ q18):=by
    intro q18 q19
    exact ((((cg (fun t => t ◇ ((q19 ◇ q18) ◇ (q18 ◇ q18))) (apc22 q18 q19)).trans (apc26 q18 q19)).symm).trans ((((cg (fun t => (((q19 ◇ q18) ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18)) ◇ t) (cg (fun t => (q19 ◇ q18) ◇ t) (apc26 q18 q19))).symm).trans (apc8 (q19 ◇ q18) (q18 ◇ q18))).trans (cg (fun t => t ◇ (q19 ◇ q18)) (apc26 q18 q19)))).symm
  have apc29 : forall (q20 q21:G), ((q21 ◇ q20) ◇ (q21 ◇ q20)) = ((q21 ◇ q20) ◇ q20):=by
    intro q20 q21
    exact ((apc27 (q21 ◇ q20) q20).symm).trans ((h (q21 ◇ q20) q20 q21).symm)
  have apc30 : forall (q22 q23:G), ((q22 ◇ q23) ◇ (q23 ◇ q22)) = ((q22 ◇ q23) ◇ q23):=by
    intro q22 q23
    exact (((apc29 q23 q22).symm).trans (((apc27 (q22 ◇ q23) (q23 ◇ q22)).symm).trans (apc3 q22 q23 (q22 ◇ q23)))).symm
  have apc31 : forall (q24 q25:G), (((q24 ◇ q24) ◇ q25) ◇ q25) = (q25 ◇ (q24 ◇ q24)):=by
    intro q24 q25
    exact ((apc29 q25 (q24 ◇ q24)).symm).trans (apc3 q24 q24 q25)
  have apc32 : forall (q26 q27:G), (((q27 ◇ q26) ◇ q26) ◇ q26) = ((q27 ◇ q26) ◇ q26):=by
    intro q26 q27
    exact (((cg (fun t => t ◇ ((q27 ◇ q26) ◇ q26)) (apc29 q26 q27)).trans (apc29 q26 (q27 ◇ q26))).symm).trans ((((cg (fun t => ((q27 ◇ q26) ◇ (q27 ◇ q26)) ◇ t) (apc29 q26 q27)).symm).trans (apc27 (q27 ◇ q26) (q27 ◇ q26))).trans (apc29 q26 q27))
  have apc33 : forall (q28 q29:G), ((q29 ◇ (q28 ◇ q28)) ◇ q29) = (q29 ◇ (q28 ◇ q28)):=by
    intro q28 q29
    exact ((((apc0 (q28 ◇ q28) q29).trans (apc31 q28 q29)).symm).trans ((((cg (fun t => t ◇ (q29 ◇ ((q28 ◇ q28) ◇ q29))) (apc31 q28 q29)).symm).trans (apc30 ((q28 ◇ q28) ◇ q29) q29)).trans (cg (fun t => t ◇ q29) (apc31 q28 q29)))).symm
  have apc34 : forall (q30 q31:G), (q31 ◇ ((q30 ◇ q31) ◇ q31)) = (q31 ◇ (q30 ◇ q31)):=by
    intro q30 q31
    exact (((apc2 q31 (q30 ◇ q31) (((q31 ◇ (q30 ◇ q31)) ◇ q31) ◇ ((q30 ◇ q31) ◇ q31))).symm).trans (((cg (fun t => ((q31 ◇ (q30 ◇ q31)) ◇ q31) ◇ t) (apc32 q31 q30)).symm).trans (apc3 q31 (q30 ◇ q31) q31))).symm
  have apc35 : forall (q32 q33:G), ((q32 ◇ q33) ◇ q33) = (q33 ◇ (q32 ◇ q33)):=by
    intro q32 q33
    exact ((((((cg (fun t => t ◇ ((q32 ◇ q33) ◇ q33)) (cg (fun t => t ◇ q33) (apc29 q33 (q32 ◇ q33)))).trans (cg (fun t => t ◇ ((q32 ◇ q33) ◇ q33)) (cg (fun t => t ◇ q33) (apc32 q33 q32)))).trans (cg (fun t => t ◇ ((q32 ◇ q33) ◇ q33)) (apc32 q33 q32))).trans (apc29 q33 (q32 ◇ q33))).trans (apc32 q33 q32)).symm).trans ((((cg (fun t => ((((q32 ◇ q33) ◇ q33) ◇ ((q32 ◇ q33) ◇ q33)) ◇ q33) ◇ t) (apc32 q33 q32)).symm).trans (apc20 q33 ((q32 ◇ q33) ◇ q33))).trans (apc34 q32 q33))
  have apc36 : forall (q34 q35:G), ((q35 ◇ q34) ◇ q34) = ((q34 ◇ q35) ◇ q35):=by
    intro q34 q35
    exact (((apc30 q34 q35).symm).trans ((((cg (fun t => t ◇ (q35 ◇ q34)) (apc2 q34 q35 q34)).symm).trans (apc35 ((q34 ◇ q35) ◇ q34) (q35 ◇ q34))).trans ((cg (fun t => (q35 ◇ q34) ◇ t) (apc2 q34 q35 (((q34 ◇ q35) ◇ q34) ◇ (q35 ◇ q34)))).trans (apc30 q35 q34)))).symm
  have apc37 : forall (q36 q37:G), ((q36 ◇ q37) ◇ q37) = (q36 ◇ (q37 ◇ q36)):=by
    intro q36 q37
    exact (((apc35 q37 q36).symm).trans (apc36 q36 q37)).symm
  have apc38 : forall (q38 q39:G), (q39 ◇ (q38 ◇ q39)) = (q38 ◇ (q39 ◇ q38)):=by
    intro q38 q39
    exact (((apc37 q38 q39).symm).trans (apc35 q38 q39)).symm
  have apc40 : forall (q40 q41:G), (q41 ◇ ((q40 ◇ q40) ◇ q41)) = (q40 ◇ q40):=by
    intro q40 q41
    exact ((apc38 q41 (q40 ◇ q40)).symm).trans ((((cg (fun t => t ◇ (q41 ◇ (q40 ◇ q40))) (apc27 q40 q40)).symm).trans (apc27 (q40 ◇ q40) q41)).trans (apc27 q40 q40))
  have apc41 : forall (q42 q43:G), (q43 ◇ (q42 ◇ q42)) = (q42 ◇ q42):=by
    intro q42 q43
    exact ((((cg (fun t => ((q42 ◇ q42) ◇ q43) ◇ t) (apc31 q42 q43)).trans (apc30 (q42 ◇ q42) q43)).trans (apc31 q42 q43)).symm).trans ((((cg (fun t => t ◇ (((q42 ◇ q42) ◇ q43) ◇ q43)) (cg (fun t => t ◇ q43) (apc40 q42 q43))).symm).trans (apc2 q43 ((q42 ◇ q42) ◇ q43) q42)).trans (apc40 q42 q43))
  have apc43 : forall (q28 q29 q42 q43:G), ((q28 ◇ q28) ◇ q29) = (q28 ◇ q28):=by
    intro q28 q29 q42 q43
    exact ((cg (fun t => t ◇ q29) (apc41 q28 q29)).symm).trans ((apc33 q28 q29).trans (apc41 q28 q29))
  have apc46 : forall (q44 q45 q46:G), (q45 ◇ q46) = (q44 ◇ q44):=by
    intro q44 q45 q46
    exact ((((cg (fun t => t ◇ (q46 ◇ q45)) (apc43 q44 q45 ((q44 ◇ q44) ◇ q45) ((q44 ◇ q44) ◇ q45))).trans (apc43 q44 (q46 ◇ q45) ((q44 ◇ q44) ◇ (q46 ◇ q45)) ((q44 ◇ q44) ◇ (q46 ◇ q45)))).symm).trans (((cg (fun t => t ◇ (q46 ◇ q45)) (cg (fun t => t ◇ q45) (apc43 q44 q46 q44 q44))).symm).trans ((h q45 q46 (q44 ◇ q44)).symm))).symm
  exact (apc46 (x ◇ (x ◇ y)) x (x ◇ y)).trans ((apc46 (x ◇ (x ◇ y)) y ((y ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49131_to_54787 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49131_to_54787
