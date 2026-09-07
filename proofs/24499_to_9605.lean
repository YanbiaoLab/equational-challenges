-- Equation24499 → Equation9605
-- Recorded verdict: true
-- Premise: x = ((y * z) * x) * ((x * y) * y)
-- Conclusion: x = y * ((z * x) * (y * (x * w)))
-- Original submission SHA-256: 074221be2f408c2043139557ba096f837ca30cb70010a88aa333a9be7b10130b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ ((x ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ x) ◇ (y ◇ (x ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ ((((q2 ◇ q0) ◇ q0) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1))) = ((q2 ◇ q0) ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((((q2 ◇ q0) ◇ q0) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1))) ((h q2 q0 q1).symm)).symm).trans ((h ((q2 ◇ q0) ◇ q0) (q0 ◇ q1) q2).symm)
  have apc3 : forall (q3 q4 q5:G), ((((q5 ◇ q3) ◇ q3) ◇ q4) ◇ ((q4 ◇ q5) ◇ q5)) = q4:=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ ((q4 ◇ q5) ◇ q5)) (cg (fun t => t ◇ q4) (apc2 q3 q3 q5))).symm).trans ((h q4 q5 ((((q5 ◇ q3) ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3))).symm)
  have apc4 : forall (q6 q7:G), (q6 ◇ ((((q6 ◇ q7) ◇ q7) ◇ q7) ◇ q7)) = ((q6 ◇ q7) ◇ q7):=by
    intro q6 q7
    exact ((cg (fun t => t ◇ ((((q6 ◇ q7) ◇ q7) ◇ q7) ◇ q7)) ((h q6 q7 q6).symm)).symm).trans (apc3 q6 ((q6 ◇ q7) ◇ q7) q7)
  have apc5 : forall (q8 q0 q1 q9:G), ((q8 ◇ q9) ◇ ((q9 ◇ ((q0 ◇ q1) ◇ q8)) ◇ ((q0 ◇ q1) ◇ q8))) = q9:=by
    intro q8 q0 q1 q9
    exact ((cg (fun t => t ◇ ((q9 ◇ ((q0 ◇ q1) ◇ q8)) ◇ ((q0 ◇ q1) ◇ q8))) (cg (fun t => t ◇ q9) ((h q8 q0 q1).symm))).symm).trans ((h q9 ((q0 ◇ q1) ◇ q8) ((q8 ◇ q0) ◇ q0)).symm)
  have apc6 : forall (q10 q11 q12:G), ((q11 ◇ q12) ◇ ((q12 ◇ (q10 ◇ q11)) ◇ (q10 ◇ q11))) = q12:=by
    intro q10 q11 q12
    exact ((cg (fun t => t ◇ ((q12 ◇ (q10 ◇ q11)) ◇ (q10 ◇ q11))) (cg (fun t => t ◇ q12) (apc5 q10 q10 q10 q11))).symm).trans ((h q12 (q10 ◇ q11) ((q11 ◇ ((q10 ◇ q10) ◇ q10)) ◇ ((q10 ◇ q10) ◇ q10))).symm)
  have apc11 : forall (q13 q14 q15:G), (q15 ◇ ((((q15 ◇ q14) ◇ q14) ◇ ((q14 ◇ q13) ◇ q13)) ◇ ((q14 ◇ q13) ◇ q13))) = ((q15 ◇ q14) ◇ q14):=by
    intro q13 q14 q15
    exact ((cg (fun t => q15 ◇ t) (cg (fun t => (((q15 ◇ q14) ◇ q14) ◇ ((q14 ◇ q13) ◇ q13)) ◇ t) (apc2 q13 q13 q14))).symm).trans (((cg (fun t => q15 ◇ t) (cg (fun t => t ◇ (q14 ◇ ((((q14 ◇ q13) ◇ q13) ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13)))) (cg (fun t => ((q15 ◇ q14) ◇ q14) ◇ t) (apc2 q13 q13 q14)))).symm).trans (apc2 q14 ((((q14 ◇ q13) ◇ q13) ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13)) q15))
  have apc12 : forall (q16 q17:G), (q16 ◇ (q17 ◇ ((q17 ◇ q16) ◇ q16))) = ((q16 ◇ q17) ◇ q17):=by
    intro q16 q17
    exact ((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ ((q17 ◇ q16) ◇ q16)) ((h q17 q16 q17).symm))).symm).trans (apc11 q16 q17 q16)
  have apc13 : forall (q18 q19:G), (((q18 ◇ q19) ◇ q19) ◇ q19) = ((q18 ◇ q19) ◇ (q19 ◇ ((q19 ◇ q18) ◇ q18))):=by
    intro q18 q19
    exact (((cg (fun t => (q18 ◇ q19) ◇ t) (cg (fun t => t ◇ ((q19 ◇ q18) ◇ q18)) (apc3 q19 q19 q18))).symm).trans (apc11 q18 q19 (q18 ◇ q19))).symm
  have apc28 : forall (q20 q21:G), (q20 ◇ (((q20 ◇ q21) ◇ q21) ◇ (q21 ◇ ((q21 ◇ (q20 ◇ q21)) ◇ (q20 ◇ q21))))) = ((q20 ◇ q21) ◇ q21):=by
    intro q20 q21
    exact ((cg (fun t => q20 ◇ t) (apc13 (q20 ◇ q21) q21)).symm).trans (apc4 q20 q21)
  have apc30 : forall (q22:G), (((q22 ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) = ((q22 ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)):=by
    intro q22
    exact ((((cg (fun t => (q22 ◇ (q22 ◇ q22)) ◇ t) (cg (fun t => (((q22 ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) ◇ t) (apc12 (q22 ◇ q22) q22))).trans (cg (fun t => (q22 ◇ (q22 ◇ q22)) ◇ t) (apc3 (q22 ◇ q22) (q22 ◇ q22) q22))).symm).trans (((cg (fun t => (q22 ◇ (q22 ◇ q22)) ◇ t) (cg (fun t => (((q22 ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) ◇ t) (cg (fun t => (q22 ◇ q22) ◇ t) (cg (fun t => t ◇ ((q22 ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22))) (apc6 q22 q22 q22))))).symm).trans (apc28 (q22 ◇ (q22 ◇ q22)) (q22 ◇ q22)))).symm
  have apc31 : forall (q23:G), (q23 ◇ ((q23 ◇ (q23 ◇ q23)) ◇ (q23 ◇ q23))) = ((q23 ◇ (q23 ◇ q23)) ◇ (q23 ◇ q23)):=by
    intro q23
    exact ((cg (fun t => q23 ◇ t) (apc30 q23)).symm).trans (((cg (fun t => q23 ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (apc30 q23))).symm).trans (apc4 q23 (q23 ◇ q23)))
  have apc32 : forall (q24:G), (((q24 ◇ q24) ◇ q24) ◇ q24) = q24:=by
    intro q24
    exact (((apc6 q24 q24 q24).symm).trans (((cg (fun t => (q24 ◇ q24) ◇ t) (apc31 q24)).symm).trans (apc12 (q24 ◇ q24) q24))).symm
  have apc33 : forall (q25:G), (q25 ◇ q25) = q25:=by
    intro q25
    exact ((((cg (fun t => ((q25 ◇ q25) ◇ q25) ◇ t) (apc32 q25)).trans (apc32 q25)).symm).trans ((((cg (fun t => ((q25 ◇ q25) ◇ q25) ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => t ◇ q25) (cg (fun t => t ◇ q25) (apc32 q25))))).symm).trans (apc4 ((q25 ◇ q25) ◇ q25) q25)).trans (cg (fun t => t ◇ q25) (apc32 q25)))).symm
  have apc34 : forall (q26 q27:G), (((q26 ◇ q27) ◇ q26) ◇ q26) = q26:=by
    intro q26 q27
    exact ((cg (fun t => ((q26 ◇ q27) ◇ q26) ◇ t) (apc33 q26)).symm).trans (((cg (fun t => ((q26 ◇ q27) ◇ q26) ◇ t) (cg (fun t => t ◇ q26) (apc33 q26))).symm).trans ((h q26 q26 q27).symm))
  have apc35 : forall (q28 q29:G), ((q29 ◇ q28) ◇ q29) = q29:=by
    intro q28 q29
    exact (((cg (fun t => (q29 ◇ q28) ◇ t) (cg (fun t => t ◇ q29) (apc33 q29))).trans (cg (fun t => (q29 ◇ q28) ◇ t) (apc33 q29))).symm).trans ((((cg (fun t => (q29 ◇ q28) ◇ t) (cg (fun t => t ◇ q29) (cg (fun t => t ◇ q29) (apc34 q29 q28)))).symm).trans (apc4 (q29 ◇ q28) q29)).trans (apc34 q29 q28))
  have apc36 : forall (q30 q31:G), (q31 ◇ q30) = q31:=by
    intro q30 q31
    exact (((((cg (fun t => (q31 ◇ q30) ◇ t) (cg (fun t => t ◇ q31) (apc35 q30 q31))).trans (cg (fun t => (q31 ◇ q30) ◇ t) (apc33 q31))).trans (apc35 q30 q31)).symm).trans (((cg (fun t => t ◇ (((q31 ◇ q30) ◇ q31) ◇ q31)) (apc35 q30 (q31 ◇ q30))).symm).trans (apc3 q30 (q31 ◇ q30) q31))).symm
  have apc37 : forall (x y z q30 q31:G), y = x:=by
    intro x y z q30 q31
    exact ((h x y x).trans (((((cg (fun t => ((y ◇ x) ◇ x) ◇ t) (cg (fun t => t ◇ y) (apc36 y x))).trans (cg (fun t => t ◇ (x ◇ y)) (cg (fun t => t ◇ x) (apc36 x y)))).trans (cg (fun t => (y ◇ x) ◇ t) (apc36 y x))).trans (cg (fun t => t ◇ x) (apc36 x y))).trans (apc36 x y))).symm
  exact (apc37 x x x x x).trans ((apc37 x (y ◇ ((z ◇ x) ◇ (y ◇ (x ◇ w)))) x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24499_to_9605 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24499_to_9605
