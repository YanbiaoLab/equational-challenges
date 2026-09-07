-- Equation41908 → Equation51256
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (z ◇ (y ◇ y)))
-- Conclusion: x ◇ x = ((y ◇ x) ◇ (z ◇ z)) ◇ x
-- Original submission SHA-256: 631f5c80158946d9240fbc4ed616b68c3bc8acd9b6948efbb6911fd50e2bda6a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (z ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ x) ◇ (z ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) ((h q1 q0 (q0 ◇ q0)).symm)).symm).trans ((h q0 (q0 ◇ q0) q1).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ (q2 ◇ (q3 ◇ (q3 ◇ q3)))) = (q2 ◇ q3):=by
    intro q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (apc0 q3 q3))).symm).trans ((h q2 q3 (q3 ◇ q3)).symm)
  have apc2 : forall (q4:G), ((q4 ◇ (q4 ◇ q4)) ◇ q4) = ((q4 ◇ q4) ◇ q4):=by
    intro q4
    exact ((((cg (fun t => q4 ◇ t) (cg (fun t => (q4 ◇ q4) ◇ t) (apc0 q4 q4))).trans (apc1 (q4 ◇ q4) q4)).symm).trans ((((cg (fun t => q4 ◇ t) (apc0 (q4 ◇ q4) q4)).symm).trans (apc1 ((q4 ◇ q4) ◇ (q4 ◇ q4)) q4)).trans (cg (fun t => t ◇ q4) (apc0 q4 q4)))).symm
  have apc3 : forall (x y z:G), (y ◇ (x ◇ (z ◇ (y ◇ y)))) = (y ◇ (x ◇ (x ◇ (y ◇ y)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc4 : forall (x y z:G), (y ◇ (x ◇ (x ◇ (y ◇ y)))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc3 x y x)).symm
  have apc5 : forall (q3:G), (q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ (q3 ◇ q3)))) = ((q3 ◇ q3) ◇ q3):=by
    intro q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => (q3 ◇ q3) ◇ t) (apc0 q3 q3))).symm).trans ((((cg (fun t => q3 ◇ t) (apc0 (q3 ◇ q3) q3)).symm).trans ((h ((q3 ◇ q3) ◇ (q3 ◇ q3)) q3 q3).symm)).trans ((cg (fun t => t ◇ q3) (apc0 q3 q3)).trans (apc2 q3)))
  have apc6 : forall (q5 q6:G), ((q5 ◇ (q5 ◇ q5)) ◇ (q6 ◇ (q5 ◇ q5))) = ((q5 ◇ q5) ◇ (q5 ◇ (q5 ◇ q5))):=by
    intro q5 q6
    exact (((cg (fun t => t ◇ (q6 ◇ (q5 ◇ q5))) (apc0 q5 q5)).symm).trans (apc0 (q5 ◇ q5) q6)).trans (cg (fun t => (q5 ◇ q5) ◇ t) (apc0 q5 q5))
  have apc7 : forall (q7 q2 q8:G), ((q7 ◇ q7) ◇ (q2 ◇ (q8 ◇ (q7 ◇ (q7 ◇ q7))))) = (q2 ◇ (q7 ◇ q7)):=by
    intro q7 q2 q8
    exact ((cg (fun t => (q7 ◇ q7) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q8 ◇ t) (apc0 q7 q7)))).symm).trans ((h q2 (q7 ◇ q7) q8).symm)
  have apc9 : forall (q9 q10:G), ((q10 ◇ (q10 ◇ q10)) ◇ (q9 ◇ ((q10 ◇ q10) ◇ q10))) = (q9 ◇ (q10 ◇ (q10 ◇ q10))):=by
    intro q9 q10
    exact ((cg (fun t => t ◇ (q9 ◇ ((q10 ◇ q10) ◇ q10))) (apc0 q10 q10)).symm).trans ((((cg (fun t => ((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ t) (cg (fun t => q9 ◇ t) ((h (q10 ◇ q10) q10 (q10 ◇ q10)).symm))).symm).trans (apc7 (q10 ◇ q10) q9 q10)).trans (cg (fun t => q9 ◇ t) (apc0 q10 q10)))
  have apc10 : forall (q5 q11:G), (((q11 ◇ q5) ◇ (q11 ◇ q5)) ◇ (q5 ◇ (q5 ◇ q5))) = ((q11 ◇ q5) ◇ ((q11 ◇ q5) ◇ (q11 ◇ q5))):=by
    intro q5 q11
    exact ((cg (fun t => ((q11 ◇ q5) ◇ (q11 ◇ q5)) ◇ t) (apc0 q5 q11)).symm).trans (apc0 (q11 ◇ q5) (q5 ◇ q5))
  have apc11 : forall (q12 q13:G), (((q12 ◇ q13) ◇ (q12 ◇ q13)) ◇ q13) = (q13 ◇ ((q12 ◇ q13) ◇ ((q12 ◇ q13) ◇ (q12 ◇ q13)))):=by
    intro q12 q13
    exact (((cg (fun t => q13 ◇ t) (apc10 q13 q12)).symm).trans ((h ((q12 ◇ q13) ◇ (q12 ◇ q13)) q13 q13).symm)).symm
  have apc12 : forall (q14 q0 q1:G), ((q14 ◇ (q1 ◇ q1)) ◇ (q0 ◇ ((q14 ◇ (q1 ◇ q1)) ◇ q1))) = (q0 ◇ (q14 ◇ (q1 ◇ q1))):=by
    intro q14 q0 q1
    exact ((cg (fun t => (q14 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => q0 ◇ t) ((h (q14 ◇ (q1 ◇ q1)) q1 q14).symm))).symm).trans ((h q0 (q14 ◇ (q1 ◇ q1)) q1).symm)
  have apc13 : forall (q15 q16:G), ((q15 ◇ (q16 ◇ q16)) ◇ (q16 ◇ (q16 ◇ q16))) = ((q16 ◇ q16) ◇ (q15 ◇ (q16 ◇ q16))):=by
    intro q15 q16
    exact ((cg (fun t => (q15 ◇ (q16 ◇ q16)) ◇ t) (apc0 q16 (q15 ◇ (q16 ◇ q16)))).symm).trans (apc12 q15 (q16 ◇ q16) q16)
  have apc14 : forall (q17 q18:G), ((q17 ◇ (q18 ◇ q18)) ◇ q18) = (q18 ◇ ((q18 ◇ q18) ◇ (q17 ◇ (q18 ◇ q18)))):=by
    intro q17 q18
    exact (((cg (fun t => q18 ◇ t) (apc13 q17 q18)).symm).trans ((h (q17 ◇ (q18 ◇ q18)) q18 q18).symm)).symm
  have apc15 : forall (q19 q20:G), ((q20 ◇ (q19 ◇ (q19 ◇ q19))) ◇ (q19 ◇ q19)) = ((q19 ◇ (q19 ◇ q19)) ◇ (q19 ◇ q19)):=by
    intro q19 q20
    exact (((cg (fun t => t ◇ (q19 ◇ q19)) (cg (fun t => q20 ◇ t) (apc0 q19 q19))).symm).trans (apc14 q20 (q19 ◇ q19))).trans (((cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => ((q19 ◇ q19) ◇ (q19 ◇ q19)) ◇ t) (cg (fun t => q20 ◇ t) (apc0 q19 q19)))).trans (cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => t ◇ (q20 ◇ (q19 ◇ (q19 ◇ q19)))) (apc0 q19 q19)))).trans (apc7 q19 (q19 ◇ (q19 ◇ q19)) q20))
  have apc17 : forall (q21 q22 q23:G), ((q22 ◇ q22) ◇ (q23 ◇ ((q22 ◇ q22) ◇ (q21 ◇ (q22 ◇ q22))))) = (q23 ◇ (q22 ◇ q22)):=by
    intro q21 q22 q23
    exact ((cg (fun t => (q22 ◇ q22) ◇ t) (cg (fun t => q23 ◇ t) (apc13 q21 q22))).symm).trans (apc7 q22 q23 (q21 ◇ (q22 ◇ q22)))
  have apc18 : forall (q24:G), ((q24 ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24)) = (q24 ◇ (q24 ◇ q24)):=by
    intro q24
    exact (((((cg (fun t => (q24 ◇ q24) ◇ t) (cg (fun t => (q24 ◇ q24) ◇ t) (cg (fun t => (q24 ◇ q24) ◇ t) (apc0 q24 q24)))).trans (apc7 q24 (q24 ◇ q24) (q24 ◇ q24))).trans (apc0 q24 q24)).symm).trans ((((cg (fun t => (q24 ◇ q24) ◇ t) (apc9 (q24 ◇ q24) (q24 ◇ q24))).symm).trans (apc17 ((q24 ◇ q24) ◇ (q24 ◇ q24)) q24 ((q24 ◇ q24) ◇ ((q24 ◇ q24) ◇ (q24 ◇ q24))))).trans ((cg (fun t => t ◇ (q24 ◇ q24)) (cg (fun t => (q24 ◇ q24) ◇ t) (apc0 q24 q24))).trans (apc15 q24 (q24 ◇ q24))))).symm
  have apc19 : forall (q24 q19 q20:G), ((q20 ◇ (q19 ◇ (q19 ◇ q19))) ◇ (q19 ◇ q19)) = (q19 ◇ (q19 ◇ q19)):=by
    intro q24 q19 q20
    exact (apc15 q19 q20).trans (apc18 q19)
  have apc21 : forall (q25:G), (((q25 ◇ q25) ◇ q25) ◇ (q25 ◇ (q25 ◇ q25))) = ((q25 ◇ q25) ◇ (q25 ◇ (q25 ◇ q25))):=by
    intro q25
    exact ((cg (fun t => ((q25 ◇ q25) ◇ q25) ◇ t) (apc0 q25 q25)).symm).trans ((((cg (fun t => t ◇ ((q25 ◇ q25) ◇ (q25 ◇ q25))) ((h (q25 ◇ q25) q25 (q25 ◇ q25)).symm)).symm).trans (apc19 q25 (q25 ◇ q25) q25)).trans (cg (fun t => (q25 ◇ q25) ◇ t) (apc0 q25 q25)))
  have apc24 : forall (q26 q27:G), ((q26 ◇ ((q27 ◇ q27) ◇ (q27 ◇ (q27 ◇ q27)))) ◇ q27) = ((q27 ◇ q27) ◇ q27):=by
    intro q26 q27
    exact ((((cg (fun t => q27 ◇ t) (cg (fun t => (q27 ◇ q27) ◇ t) (apc0 q27 q27))).trans (apc5 q27)).symm).trans ((((cg (fun t => q27 ◇ t) (apc19 q26 (q27 ◇ q27) q26)).symm).trans ((h (q26 ◇ ((q27 ◇ q27) ◇ ((q27 ◇ q27) ◇ (q27 ◇ q27)))) q27 (q27 ◇ q27)).symm)).trans (cg (fun t => t ◇ q27) (cg (fun t => q26 ◇ t) (cg (fun t => (q27 ◇ q27) ◇ t) (apc0 q27 q27)))))).symm
  have apc25 : forall (q28 q29:G), (((q28 ◇ q29) ◇ ((q28 ◇ q29) ◇ (q28 ◇ q29))) ◇ (q29 ◇ q29)) = (q29 ◇ (q29 ◇ q29)):=by
    intro q28 q29
    exact ((cg (fun t => t ◇ (q29 ◇ q29)) (apc10 q29 q28)).symm).trans (apc19 q28 q29 ((q28 ◇ q29) ◇ (q28 ◇ q29)))
  have apc26 : forall (q30 q31 q32:G), ((q31 ◇ q31) ◇ (q32 ◇ ((q30 ◇ q31) ◇ ((q30 ◇ q31) ◇ (q30 ◇ q31))))) = (q32 ◇ (q31 ◇ q31)):=by
    intro q30 q31 q32
    exact ((cg (fun t => (q31 ◇ q31) ◇ t) (cg (fun t => q32 ◇ t) (apc10 q31 q30))).symm).trans (apc7 q31 q32 ((q30 ◇ q31) ◇ (q30 ◇ q31)))
  have apc27 : forall (q33 q34:G), (((q33 ◇ q34) ◇ (q33 ◇ q34)) ◇ (q34 ◇ q34)) = (q34 ◇ (q34 ◇ q34)):=by
    intro q33 q34
    exact (((cg (fun t => (q34 ◇ q34) ◇ t) (cg (fun t => ((q33 ◇ q34) ◇ (q33 ◇ q34)) ◇ t) (apc0 (q33 ◇ q34) (q33 ◇ q34)))).trans (apc26 q33 q34 ((q33 ◇ q34) ◇ (q33 ◇ q34)))).symm).trans ((((cg (fun t => (q34 ◇ q34) ◇ t) (apc0 ((q33 ◇ q34) ◇ (q33 ◇ q34)) (q33 ◇ q34))).symm).trans (apc26 q33 q34 (((q33 ◇ q34) ◇ (q33 ◇ q34)) ◇ ((q33 ◇ q34) ◇ (q33 ◇ q34))))).trans ((cg (fun t => t ◇ (q34 ◇ q34)) (apc0 (q33 ◇ q34) (q33 ◇ q34))).trans (apc25 q33 q34)))
  have apc29 : forall (q35 q36 q37:G), (((q35 ◇ q36) ◇ (q35 ◇ q36)) ◇ (q37 ◇ (q36 ◇ q36))) = ((q36 ◇ q36) ◇ ((q35 ◇ q36) ◇ (q35 ◇ q36))):=by
    intro q35 q36 q37
    exact ((cg (fun t => ((q35 ◇ q36) ◇ (q35 ◇ q36)) ◇ t) (apc26 q35 q36 q37)).symm).trans (apc7 (q35 ◇ q36) (q36 ◇ q36) q37)
  have apc30 : forall (q5 q11 q35 q36 q37:G), ((q11 ◇ q5) ◇ ((q11 ◇ q5) ◇ (q11 ◇ q5))) = ((q5 ◇ q5) ◇ ((q11 ◇ q5) ◇ (q11 ◇ q5))):=by
    intro q5 q11 q35 q36 q37
    exact (((apc29 q11 q5 q5).symm).trans (apc10 q5 q11)).symm
  have apc31 : forall (q38 q39:G), (((q38 ◇ q39) ◇ (q38 ◇ q39)) ◇ q39) = (q39 ◇ ((q39 ◇ q39) ◇ ((q38 ◇ q39) ◇ (q38 ◇ q39)))):=by
    intro q38 q39
    exact (((cg (fun t => q39 ◇ t) (apc29 q38 q39 q38)).symm).trans ((h ((q38 ◇ q39) ◇ (q38 ◇ q39)) q39 q38).symm)).symm
  have apc33 : forall (q40 q41:G), (q41 ◇ ((q41 ◇ q41) ◇ ((q40 ◇ q41) ◇ (q40 ◇ q41)))) = (q41 ◇ ((q40 ◇ q41) ◇ ((q40 ◇ q41) ◇ (q40 ◇ q41)))):=by
    intro q40 q41
    exact ((apc31 q40 q41).symm).trans (apc11 q40 q41)
  have apc42 : forall (q42 q43:G), (((q42 ◇ q43) ◇ (q42 ◇ q43)) ◇ (q42 ◇ q43)) = ((q43 ◇ (q43 ◇ q43)) ◇ (q42 ◇ q43)):=by
    intro q42 q43
    exact (((cg (fun t => t ◇ (q42 ◇ q43)) (apc27 q42 q43)).symm).trans (((cg (fun t => t ◇ (q42 ◇ q43)) (apc26 q42 q43 ((q42 ◇ q43) ◇ (q42 ◇ q43)))).symm).trans (apc24 (q43 ◇ q43) (q42 ◇ q43)))).symm
  have apc47 : forall (q44:G), ((q44 ◇ q44) ◇ (((q44 ◇ q44) ◇ q44) ◇ ((q44 ◇ q44) ◇ q44))) = ((q44 ◇ q44) ◇ (q44 ◇ (q44 ◇ q44))):=by
    intro q44
    exact ((((apc9 (q44 ◇ (q44 ◇ q44)) q44).trans (apc6 q44 q44)).symm).trans ((((cg (fun t => (q44 ◇ (q44 ◇ q44)) ◇ t) (apc42 (q44 ◇ q44) q44)).symm).trans (apc9 (((q44 ◇ q44) ◇ q44) ◇ ((q44 ◇ q44) ◇ q44)) q44)).trans (apc29 (q44 ◇ q44) q44 q44))).symm
  have apc49 : forall (q45 q46:G), ((q45 ◇ q46) ◇ (q46 ◇ ((q45 ◇ q46) ◇ ((q45 ◇ q46) ◇ (q45 ◇ q46))))) = (q46 ◇ (q45 ◇ q46)):=by
    intro q45 q46
    exact ((cg (fun t => (q45 ◇ q46) ◇ t) (apc33 q45 q46)).symm).trans ((h q46 (q45 ◇ q46) (q46 ◇ q46)).symm)
  have apc50 : forall (q47:G), (((q47 ◇ q47) ◇ q47) ◇ ((q47 ◇ q47) ◇ q47)) = (q47 ◇ ((q47 ◇ q47) ◇ q47)):=by
    intro q47
    exact (((((((cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (cg (fun t => q47 ◇ t) (cg (fun t => ((q47 ◇ (q47 ◇ q47)) ◇ q47) ◇ t) (cg (fun t => t ◇ ((q47 ◇ (q47 ◇ q47)) ◇ q47)) (apc2 q47))))).trans (cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (cg (fun t => q47 ◇ t) (cg (fun t => ((q47 ◇ (q47 ◇ q47)) ◇ q47) ◇ t) (cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (apc2 q47)))))).trans (cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (cg (fun t => q47 ◇ t) (cg (fun t => t ◇ (((q47 ◇ q47) ◇ q47) ◇ ((q47 ◇ q47) ◇ q47))) (apc2 q47))))).trans (cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (cg (fun t => q47 ◇ t) (apc30 q47 (q47 ◇ q47) (((q47 ◇ q47) ◇ q47) ◇ (((q47 ◇ q47) ◇ q47) ◇ ((q47 ◇ q47) ◇ q47))) (((q47 ◇ q47) ◇ q47) ◇ (((q47 ◇ q47) ◇ q47) ◇ ((q47 ◇ q47) ◇ q47))) (((q47 ◇ q47) ◇ q47) ◇ (((q47 ◇ q47) ◇ q47) ◇ ((q47 ◇ q47) ◇ q47))))))).trans (cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (cg (fun t => q47 ◇ t) (apc47 q47)))).trans (cg (fun t => ((q47 ◇ q47) ◇ q47) ◇ t) (apc5 q47))).symm).trans ((((cg (fun t => t ◇ (q47 ◇ (((q47 ◇ (q47 ◇ q47)) ◇ q47) ◇ (((q47 ◇ (q47 ◇ q47)) ◇ q47) ◇ ((q47 ◇ (q47 ◇ q47)) ◇ q47))))) (apc2 q47)).symm).trans (apc49 (q47 ◇ (q47 ◇ q47)) q47)).trans (cg (fun t => q47 ◇ t) (apc2 q47)))
  have apc51 : forall (q48:G), ((q48 ◇ q48) ◇ (q48 ◇ (q48 ◇ q48))) = (q48 ◇ (q48 ◇ (q48 ◇ q48))):=by
    intro q48
    exact (((apc9 q48 q48).symm).trans ((((cg (fun t => (q48 ◇ (q48 ◇ q48)) ◇ t) (apc50 q48)).symm).trans (apc9 ((q48 ◇ q48) ◇ q48) q48)).trans (apc21 q48))).symm
  have apc52 : forall (q49:G), ((q49 ◇ q49) ◇ q49) = (q49 ◇ q49):=by
    intro q49
    exact (((apc4 q49 q49 (q49 ◇ (q49 ◇ (q49 ◇ (q49 ◇ q49))))).symm).trans (((cg (fun t => q49 ◇ t) (apc51 q49)).symm).trans ((h (q49 ◇ q49) q49 q49).symm))).symm
  have apc60 : forall (q5 q6 q48:G), ((q5 ◇ (q5 ◇ q5)) ◇ (q6 ◇ (q5 ◇ q5))) = (q5 ◇ (q5 ◇ (q5 ◇ q5))):=by
    intro q5 q6 q48
    exact (apc6 q5 q6).trans (apc51 q5)
  have apc62 : forall (q9 q10 q49:G), (q10 ◇ (q10 ◇ (q10 ◇ q10))) = (q9 ◇ (q10 ◇ (q10 ◇ q10))):=by
    intro q9 q10 q49
    exact ((apc60 q10 q9 ((q10 ◇ (q10 ◇ q10)) ◇ (q9 ◇ (q10 ◇ q10)))).symm).trans (((cg (fun t => (q10 ◇ (q10 ◇ q10)) ◇ t) (cg (fun t => q9 ◇ t) (apc52 q10))).symm).trans (apc9 q9 q10))
  have apc63 : forall (q50 q51:G), (q51 ◇ q51) = (q50 ◇ q51):=by
    intro q50 q51
    exact ((apc4 q51 q51 (q51 ◇ (q51 ◇ (q51 ◇ (q51 ◇ q51))))).symm).trans (((cg (fun t => q51 ◇ t) ((apc62 q50 q51 q50).symm)).symm).trans ((h q50 q51 q51).symm))
  exact (apc63 x x).trans (apc63 ((y ◇ x) ◇ (z ◇ z)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41908_to_51256 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41908_to_51256
