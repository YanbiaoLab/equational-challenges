-- Equation48096 → Equation44033
-- Recorded verdict: true
-- Premise: x * y = (y * (z * x)) * (x * x)
-- Conclusion: x * y = z * ((w * x) * (z * u))
-- Original submission SHA-256: 434effe90abe04f6a1787a17dc3a2df2aa815ce63b4c2ce4c2df3f1dedb0f797
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (z ◇ x)) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ ((w ◇ x) ◇ (z ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q1 ◇ q2))) = ((q2 ◇ q0) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q2 ◇ q2)) ((h q2 q0 q1).symm)).symm).trans ((h q2 (q0 ◇ (q1 ◇ q2)) q2).symm)).symm
  have apc2 : forall (x y z:G), ((y ◇ (z ◇ x)) ◇ (x ◇ x)) = ((y ◇ (x ◇ x)) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc3 : forall (q3 q4:G), ((q4 ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) = (q3 ◇ q4):=by
    intro q3 q4
    exact ((apc2 q3 q4 q3).symm).trans ((h q3 q4 q3).symm)
  have apc4 : forall (q5 q0 q6:G), ((q6 ◇ (q5 ◇ q0)) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5))) = ((q5 ◇ q5) ◇ q6):=by
    intro q5 q0 q6
    exact ((cg (fun t => t ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5))) (cg (fun t => q6 ◇ t) ((h q5 q0 q5).symm))).symm).trans ((h (q5 ◇ q5) q6 (q0 ◇ (q5 ◇ q5))).symm)
  have apc5 : forall (q7 q8:G), (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ q8) = ((q7 ◇ q7) ◇ q8):=by
    intro q7 q8
    exact ((((cg (fun t => (q8 ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) ◇ t) (apc4 q7 q7 (q7 ◇ q7))).trans (apc3 (q7 ◇ q7) q8)).symm).trans (((cg (fun t => t ◇ (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7)))) (cg (fun t => q8 ◇ t) (apc4 q7 q7 (q7 ◇ q7)))).symm).trans (apc3 ((q7 ◇ q7) ◇ (q7 ◇ q7)) q8))).symm
  have apc6 : forall (q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = (q9 ◇ (q9 ◇ q9)):=by
    intro q9
    exact ((apc5 q9 (q9 ◇ q9)).symm).trans ((h q9 (q9 ◇ q9) q9).symm)
  have apc7 : forall (q10:G), (q10 ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10
    exact (((apc3 q10 q10).symm).trans (((cg (fun t => t ◇ (q10 ◇ q10)) (apc6 q10)).symm).trans ((h q10 (q10 ◇ q10) q10).symm))).symm
  have apc8 : forall (q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = (q9 ◇ q9):=by
    intro q9
    exact (apc6 q9).trans (apc7 q9)
  have apc9 : forall (q11 q12:G), ((q11 ◇ q11) ◇ q12) = (q11 ◇ q12):=by
    intro q11 q12
    exact ((((cg (fun t => (q12 ◇ (q11 ◇ q11)) ◇ t) (apc8 q11)).trans (apc3 q11 q12)).symm).trans (((cg (fun t => t ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (cg (fun t => q12 ◇ t) (apc8 q11))).symm).trans ((h (q11 ◇ q11) q12 (q11 ◇ q11)).symm))).symm
  have apc10 : forall (q13 q14 q15:G), (((q14 ◇ q15) ◇ (q14 ◇ q14)) ◇ ((q13 ◇ q14) ◇ (q13 ◇ q14))) = ((q13 ◇ q14) ◇ q14):=by
    intro q13 q14 q15
    exact ((cg (fun t => t ◇ ((q13 ◇ q14) ◇ (q13 ◇ q14))) (apc0 q15 q13 q14)).symm).trans ((h (q13 ◇ q14) q14 q15).symm)
  have apc11 : forall (q16 q17:G), (q16 ◇ (q16 ◇ q17)) = (q16 ◇ q16):=by
    intro q16 q17
    exact ((((((((cg (fun t => t ◇ ((q16 ◇ q16) ◇ (q16 ◇ (q16 ◇ q16)))) (cg (fun t => t ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) (apc9 q16 q17))).trans (cg (fun t => ((q16 ◇ q17) ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) ◇ t) (cg (fun t => (q16 ◇ q16) ◇ t) (apc7 q16)))).trans (cg (fun t => t ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) (cg (fun t => (q16 ◇ q17) ◇ t) (apc9 q16 (q16 ◇ q16))))).trans (cg (fun t => t ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) (cg (fun t => (q16 ◇ q17) ◇ t) (apc7 q16)))).trans (cg (fun t => ((q16 ◇ q17) ◇ (q16 ◇ q16)) ◇ t) (apc9 q16 (q16 ◇ q16)))).trans (cg (fun t => ((q16 ◇ q17) ◇ (q16 ◇ q16)) ◇ t) (apc7 q16))).trans (apc3 q16 (q16 ◇ q17))).symm).trans ((((cg (fun t => (((q16 ◇ q16) ◇ q17) ◇ ((q16 ◇ q16) ◇ (q16 ◇ q16))) ◇ t) (cg (fun t => t ◇ (q16 ◇ (q16 ◇ q16))) (apc7 q16))).symm).trans (apc10 q16 (q16 ◇ q16) q17)).trans (((cg (fun t => t ◇ (q16 ◇ q16)) (apc7 q16)).trans (apc9 q16 (q16 ◇ q16))).trans (apc7 q16)))
  have apc12 : forall (q18 q19:G), (q19 ◇ (q18 ◇ q18)) = (q18 ◇ q19):=by
    intro q18 q19
    exact ((apc9 q19 (q18 ◇ q18)).symm).trans (((cg (fun t => t ◇ (q18 ◇ q18)) (apc11 q19 q18)).symm).trans ((h q18 q19 q19).symm))
  have apc13 : forall (q20 q21:G), (q21 ◇ q20) = (q20 ◇ q21):=by
    intro q20 q21
    exact ((apc12 q21 q20).symm).trans ((((apc12 q20 (q21 ◇ q21)).symm).trans (apc9 q21 (q20 ◇ q20))).trans (apc12 q20 q21))
  have apc14 : forall (q22 q23:G), ((q22 ◇ q23) ◇ q22) = (q22 ◇ q23):=by
    intro q22 q23
    exact ((((apc13 (q22 ◇ q22) (q22 ◇ q23)).trans (apc9 q22 (q22 ◇ q23))).trans (apc13 (q22 ◇ q23) q22)).symm).trans (((cg (fun t => t ◇ (q22 ◇ q22)) (apc12 q22 q23)).symm).trans ((h q22 q23 q22).symm))
  have apc15 : forall (q24 q25:G), (q24 ◇ q25) = (q24 ◇ q24):=by
    intro q24 q25
    exact (((((cg (fun t => (q24 ◇ q24) ◇ t) (apc13 q24 q25)).trans (apc9 q24 (q24 ◇ q25))).trans (apc13 (q24 ◇ q25) q24)).trans (apc14 q24 q25)).symm).trans ((((apc14 (q24 ◇ q24) (q25 ◇ q24)).symm).trans ((h q24 (q24 ◇ q24) q25).symm)).trans ((apc13 (q24 ◇ q24) q24).trans (apc9 q24 q24)))
  have apc17 : forall (q20 q21:G), (q21 ◇ q20) = (q20 ◇ q20):=by
    intro q20 q21
    exact (apc13 q20 q21).trans (apc15 q20 q21)
  have apc18 : forall (q26 q27:G), (q27 ◇ q27) = (q26 ◇ q26):=by
    intro q26 q27
    exact ((apc17 q27 q26).symm).trans (apc15 q26 q27)
  exact (calc
    (x ◇ y) = (x ◇ x):=apc15 x y
    _ = (z ◇ z):=apc18 z x
    _ = (z ◇ ((w ◇ x) ◇ (z ◇ u))):=(apc15 z ((w ◇ x) ◇ (z ◇ u))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48096_to_44033 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48096_to_44033
