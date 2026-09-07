-- Equation48331 → Equation43488
-- Recorded verdict: true
-- Premise: x * y = (z * (z * x)) * (y * x)
-- Conclusion: x * y = x * ((x * x) * (x * z))
-- Original submission SHA-256: 53cc4ac7599c3a5deae5c703517945d11f1950de1e241798a1103de14711d5c5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (z ◇ x)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ ((x ◇ x) ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((z ◇ (z ◇ x)) ◇ (y ◇ x)) = ((x ◇ (x ◇ x)) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ x)) ◇ (y ◇ x)) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2:G), ((q1 ◇ (q0 ◇ (q0 ◇ q1))) ◇ (q2 ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ q1)) ((h q1 (q0 ◇ (q0 ◇ q1)) q0).symm)).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q1))).symm)
  have apc3 : forall (q3 q4 q0 q5:G), ((q5 ◇ (q5 ◇ (q4 ◇ q3))) ◇ (q3 ◇ q4)) = ((q4 ◇ q3) ◇ (q0 ◇ (q0 ◇ q3))):=by
    intro q3 q4 q0 q5
    exact ((cg (fun t => (q5 ◇ (q5 ◇ (q4 ◇ q3))) ◇ t) ((h q3 q4 q0).symm)).symm).trans ((h (q4 ◇ q3) (q0 ◇ (q0 ◇ q3)) q5).symm)
  have apc4 : forall (q6 q7:G), ((q7 ◇ q7) ◇ (q6 ◇ (q6 ◇ q7))) = (q7 ◇ q7):=by
    intro q6 q7
    exact ((apc3 q7 q7 q6 q7).symm).trans (apc2 q7 q7 q7)
  have apc5 : forall (q3 q4 q0 q5:G), ((q4 ◇ q3) ◇ (q0 ◇ (q0 ◇ q3))) = ((q4 ◇ q3) ◇ (q3 ◇ (q3 ◇ q3))):=by
    intro q3 q4 q0 q5
    exact ((apc3 q3 q4 q0 q3).symm).trans (apc3 q3 q4 q3 q3)
  have apc7 : forall (q8 q9:G), ((q9 ◇ q9) ◇ (q9 ◇ (q8 ◇ (q8 ◇ q9)))) = (q9 ◇ q9):=by
    intro q8 q9
    exact ((cg (fun t => (q9 ◇ q9) ◇ t) ((h q9 (q8 ◇ (q8 ◇ q9)) q8).symm)).symm).trans (apc4 (q8 ◇ (q8 ◇ q9)) q9)
  have apc8 : forall (q10 q11:G), ((q10 ◇ q10) ◇ (q11 ◇ (q10 ◇ q10))) = ((q10 ◇ q10) ◇ q11):=by
    intro q10 q11
    exact ((cg (fun t => t ◇ (q11 ◇ (q10 ◇ q10))) (apc7 q10 q10)).symm).trans (apc2 q10 (q10 ◇ q10) q11)
  have apc9 : forall (q12:G), ((q12 ◇ q12) ◇ q12) = (q12 ◇ q12):=by
    intro q12
    exact ((apc8 q12 q12).symm).trans (apc4 q12 q12)
  have apc10 : forall (q13:G), (q13 ◇ (q13 ◇ q13)) = (q13 ◇ q13):=by
    intro q13
    exact (((apc1 q13 q13 ((q13 ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13))).symm).trans (((cg (fun t => (q13 ◇ (q13 ◇ q13)) ◇ t) (apc9 q13)).symm).trans (apc1 q13 (q13 ◇ q13) q13))).symm
  have apc12 : forall (x y z q13:G), ((x ◇ x) ◇ (y ◇ x)) = (x ◇ y):=by
    intro x y z q13
    exact ((cg (fun t => t ◇ (y ◇ x)) (apc10 x)).symm).trans (apc1 x y x)
  have apc14 : forall (q14 q15:G), ((q15 ◇ (q15 ◇ q14)) ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q14 q15
    exact (((cg (fun t => (q15 ◇ (q15 ◇ q14)) ◇ t) (apc9 q14)).symm).trans ((h q14 (q14 ◇ q14) q15).symm)).trans (apc10 q14)
  have apc15 : forall (q16 q17 q18:G), ((q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ q17)))) ◇ (q18 ◇ q17)) = (q17 ◇ q18):=by
    intro q16 q17 q18
    exact ((cg (fun t => t ◇ (q18 ◇ q17)) (apc2 q16 q17 (q17 ◇ (q16 ◇ (q16 ◇ q17))))).symm).trans ((h q17 q18 (q17 ◇ (q16 ◇ (q16 ◇ q17)))).symm)
  have apc16 : forall (q19 q20 q21:G), ((q20 ◇ q20) ◇ (q21 ◇ (q19 ◇ (q19 ◇ q20)))) = ((q19 ◇ (q19 ◇ q20)) ◇ q21):=by
    intro q19 q20 q21
    exact ((((cg (fun t => t ◇ (q21 ◇ (q19 ◇ (q19 ◇ q20)))) (cg (fun t => (q19 ◇ (q19 ◇ q20)) ◇ t) (cg (fun t => (q19 ◇ (q19 ◇ q20)) ◇ t) (apc12 q20 q20 ((q20 ◇ q20) ◇ (q20 ◇ q20)) ((q20 ◇ q20) ◇ (q20 ◇ q20)))))).trans (cg (fun t => t ◇ (q21 ◇ (q19 ◇ (q19 ◇ q20)))) (cg (fun t => (q19 ◇ (q19 ◇ q20)) ◇ t) (apc14 q20 q19)))).trans (cg (fun t => t ◇ (q21 ◇ (q19 ◇ (q19 ◇ q20)))) (apc14 q20 q19))).symm).trans (((cg (fun t => t ◇ (q21 ◇ (q19 ◇ (q19 ◇ q20)))) (cg (fun t => (q19 ◇ (q19 ◇ q20)) ◇ t) (cg (fun t => (q19 ◇ (q19 ◇ q20)) ◇ t) (cg (fun t => (q20 ◇ q20) ◇ t) (apc4 q19 q20))))).symm).trans (apc15 (q20 ◇ q20) (q19 ◇ (q19 ◇ q20)) q21))
  have apc17 : forall (q8 q9 q19 q20 q21:G), ((q8 ◇ (q8 ◇ q9)) ◇ q9) = (q9 ◇ q9):=by
    intro q8 q9 q19 q20 q21
    exact ((apc16 q8 q9 q9).symm).trans (apc7 q8 q9)
  have apc18 : forall (q22 q23:G), (q23 ◇ (q22 ◇ (q22 ◇ q23))) = (q23 ◇ q23):=by
    intro q22 q23
    exact (((apc14 q23 q22).symm).trans (((cg (fun t => (q22 ◇ (q22 ◇ q23)) ◇ t) (apc17 q22 q23 q22 q22 q22)).symm).trans ((h q23 (q22 ◇ (q22 ◇ q23)) q22).symm))).symm
  have apc19 : forall (q24 q25:G), ((q24 ◇ (q24 ◇ q25)) ◇ (q24 ◇ (q24 ◇ q25))) = (q25 ◇ q25):=by
    intro q24 q25
    exact ((((cg (fun t => t ◇ (q24 ◇ (q24 ◇ q25))) (apc12 q25 q25 ((q25 ◇ q25) ◇ (q25 ◇ q25)) ((q25 ◇ q25) ◇ (q25 ◇ q25)))).trans (apc4 q24 q25)).symm).trans (((cg (fun t => t ◇ (q24 ◇ (q24 ◇ q25))) (cg (fun t => (q25 ◇ q25) ◇ t) (apc4 q24 q25))).symm).trans (apc17 (q25 ◇ q25) (q24 ◇ (q24 ◇ q25)) q24 q24 q24))).symm
  have apc20 : forall (q26 q27 q28:G), ((q28 ◇ (q28 ◇ (q27 ◇ q26))) ◇ (q26 ◇ q27)) = ((q27 ◇ q26) ◇ (q26 ◇ q26)):=by
    intro q26 q27 q28
    exact (((cg (fun t => (q28 ◇ (q28 ◇ (q27 ◇ q26))) ◇ t) (apc2 q26 q26 q27)).symm).trans ((h (q27 ◇ q26) (q26 ◇ (q26 ◇ (q26 ◇ q26))) q28).symm)).trans (cg (fun t => (q27 ◇ q26) ◇ t) (apc18 q26 q26))
  have apc21 : forall (q3 q4 q0 q5 q13:G), ((q4 ◇ q3) ◇ (q0 ◇ (q0 ◇ q3))) = ((q4 ◇ q3) ◇ (q3 ◇ q3)):=by
    intro q3 q4 q0 q5 q13
    exact (apc5 q3 q4 q0 q3).trans (cg (fun t => (q4 ◇ q3) ◇ t) (apc10 q3))
  have apc22 : forall (q29 q30:G), ((q30 ◇ (q29 ◇ q29)) ◇ (q30 ◇ (q29 ◇ q29))) = (q30 ◇ q30):=by
    intro q29 q30
    exact ((((cg (fun t => ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ q30)) ◇ t) (cg (fun t => (q29 ◇ q29) ◇ t) (apc8 q29 q30))).trans (apc19 (q29 ◇ q29) q30)).symm).trans (((cg (fun t => t ◇ ((q29 ◇ q29) ◇ ((q29 ◇ q29) ◇ (q30 ◇ (q29 ◇ q29))))) (cg (fun t => (q29 ◇ q29) ◇ t) (apc8 q29 q30))).symm).trans (apc19 (q29 ◇ q29) (q30 ◇ (q29 ◇ q29))))).symm
  have apc23 : forall (q31 q32:G), ((q32 ◇ q32) ◇ (q32 ◇ (q31 ◇ q31))) = (q32 ◇ q32):=by
    intro q31 q32
    exact (((cg (fun t => t ◇ (q32 ◇ (q31 ◇ q31))) (apc22 q31 q32)).symm).trans (apc9 (q32 ◇ (q31 ◇ q31)))).trans (apc22 q31 q32)
  have apc25 : forall (q33 q34:G), ((q34 ◇ (q33 ◇ q33)) ◇ (q33 ◇ q33)) = (q34 ◇ (q33 ◇ q33)):=by
    intro q33 q34
    exact ((((cg (fun t => t ◇ ((q33 ◇ q33) ◇ q34)) (apc12 q34 q34 ((q34 ◇ q34) ◇ (q34 ◇ q34)) ((q34 ◇ q34) ◇ (q34 ◇ q34)))).trans (apc12 q34 (q33 ◇ q33) ((q34 ◇ q34) ◇ ((q33 ◇ q33) ◇ q34)) ((q34 ◇ q34) ◇ ((q33 ◇ q33) ◇ q34)))).symm).trans ((((cg (fun t => t ◇ ((q33 ◇ q33) ◇ q34)) (cg (fun t => (q34 ◇ q34) ◇ t) (apc23 q33 q34))).symm).trans (apc20 (q33 ◇ q33) q34 (q34 ◇ q34))).trans (cg (fun t => (q34 ◇ (q33 ◇ q33)) ◇ t) (apc12 q33 q33 ((q33 ◇ q33) ◇ (q33 ◇ q33)) ((q33 ◇ q33) ◇ (q33 ◇ q33)))))).symm
  have apc26 : forall (q35 q36:G), (q36 ◇ q36) = (q35 ◇ q35):=by
    intro q35 q36
    exact (((((cg (fun t => ((q36 ◇ (q35 ◇ q35)) ◇ (q36 ◇ (q35 ◇ q35))) ◇ t) (cg (fun t => (q36 ◇ (q35 ◇ q35)) ◇ t) (apc25 q35 q36))).trans (cg (fun t => t ◇ ((q36 ◇ (q35 ◇ q35)) ◇ (q36 ◇ (q35 ◇ q35)))) (apc22 q35 q36))).trans (cg (fun t => (q36 ◇ q36) ◇ t) (apc22 q35 q36))).trans (apc12 q36 q36 ((q36 ◇ q36) ◇ (q36 ◇ q36)) ((q36 ◇ q36) ◇ (q36 ◇ q36)))).symm).trans ((((cg (fun t => t ◇ ((q36 ◇ (q35 ◇ q35)) ◇ ((q36 ◇ (q35 ◇ q35)) ◇ (q35 ◇ q35)))) (cg (fun t => (q36 ◇ (q35 ◇ q35)) ◇ t) (apc25 q35 q36))).symm).trans (apc19 (q36 ◇ (q35 ◇ q35)) (q35 ◇ q35))).trans (apc12 q35 q35 ((q35 ◇ q35) ◇ (q35 ◇ q35)) ((q35 ◇ q35) ◇ (q35 ◇ q35))))
  have apc29 : forall (q37 q38 q39:G), ((q37 ◇ q37) ◇ (q39 ◇ q38)) = (q38 ◇ q39):=by
    intro q37 q38 q39
    exact ((cg (fun t => t ◇ (q39 ◇ q38)) (apc26 q37 q38)).symm).trans (apc12 q38 q39 q37 q37)
  have apc30 : forall (q40 q41:G), ((q41 ◇ q40) ◇ q41) = (q40 ◇ q40):=by
    intro q40 q41
    exact (((apc29 q40 (q41 ◇ q40) q41).symm).trans (apc21 q40 q40 q41 q40 q40)).trans (apc29 q40 q40 q40)
  have apc31 : forall (q42 q43:G), (q43 ◇ q43) = (q42 ◇ q43):=by
    intro q42 q43
    exact (((apc29 q42 q42 q43).symm).trans (((cg (fun t => t ◇ (q43 ◇ q42)) (apc30 q42 q43)).symm).trans (apc30 q43 (q43 ◇ q42)))).symm
  have apc32 : forall (q44 q45 q46:G), (q45 ◇ q45) = (q44 ◇ q46):=by
    intro q44 q45 q46
    exact (((apc31 q44 q46).symm).trans (apc26 q45 q46)).symm
  exact ((apc32 x (x ◇ y) y).symm).trans (apc32 x (x ◇ y) ((x ◇ x) ◇ (x ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48331_to_43488 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48331_to_43488
