-- Equation7642 → Equation2944
-- Recorded verdict: true
-- Premise: x = y * (x * ((z * (z * y)) * y))
-- Conclusion: x = ((y * (y * x)) * z) * z
-- Original submission SHA-256: b70f71c3aa5b977f017aec9497e43cb0009578508e0a05c9bf397b09dbcbcb74
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ (z ◇ y)) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ x)) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q0 ◇ (q0 ◇ q1)) ◇ q1) ◇ (q2 ◇ (q2 ◇ ((q0 ◇ (q0 ◇ q1)) ◇ q1)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q0 ◇ (q0 ◇ q1)) ◇ q1) ◇ t) ((h (q2 ◇ (q2 ◇ ((q0 ◇ (q0 ◇ q1)) ◇ q1))) q1 q0).symm)).symm).trans ((h q1 ((q0 ◇ (q0 ◇ q1)) ◇ q1) q2).symm)
  have apc1 : forall (q3 q4:G), (((q3 ◇ (q3 ◇ q4)) ◇ q4) ◇ q4) = q4:=by
    intro q3 q4
    exact ((cg (fun t => ((q3 ◇ (q3 ◇ q4)) ◇ q4) ◇ t) ((h q4 q4 q3).symm)).symm).trans (apc0 q3 q4 q4)
  have apc2 : forall (q5 q6:G), ((q5 ◇ q5) ◇ q5) = q5:=by
    intro q5 q6
    exact ((cg (fun t => t ◇ q5) (cg (fun t => t ◇ q5) (apc1 q6 q5))).symm).trans (((cg (fun t => t ◇ q5) (cg (fun t => t ◇ q5) (cg (fun t => ((q6 ◇ (q6 ◇ q5)) ◇ q5) ◇ t) (apc1 q6 q5)))).symm).trans (apc1 ((q6 ◇ (q6 ◇ q5)) ◇ q5) q5))
  have apc3 : forall (q7 q8:G), (((q7 ◇ (q7 ◇ q8)) ◇ q8) ◇ ((q7 ◇ (q7 ◇ q8)) ◇ q8)) = q8:=by
    intro q7 q8
    exact ((cg (fun t => ((q7 ◇ (q7 ◇ q8)) ◇ q8) ◇ t) (apc2 ((q7 ◇ (q7 ◇ q8)) ◇ q8) ((((q7 ◇ (q7 ◇ q8)) ◇ q8) ◇ ((q7 ◇ (q7 ◇ q8)) ◇ q8)) ◇ ((q7 ◇ (q7 ◇ q8)) ◇ q8)))).symm).trans (((cg (fun t => ((q7 ◇ (q7 ◇ q8)) ◇ q8) ◇ t) (cg (fun t => (((q7 ◇ (q7 ◇ q8)) ◇ q8) ◇ ((q7 ◇ (q7 ◇ q8)) ◇ q8)) ◇ t) (apc2 ((q7 ◇ (q7 ◇ q8)) ◇ q8) q7))).symm).trans (apc0 q7 q8 (((q7 ◇ (q7 ◇ q8)) ◇ q8) ◇ ((q7 ◇ (q7 ◇ q8)) ◇ q8))))
  have apc4 : forall (q9 q10:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = q9:=by
    intro q9 q10
    exact ((((cg (fun t => ((((q10 ◇ (q10 ◇ q9)) ◇ q9) ◇ q9) ◇ q9) ◇ t) (cg (fun t => t ◇ q9) (cg (fun t => ((q10 ◇ (q10 ◇ q9)) ◇ q9) ◇ t) (apc1 q10 q9)))).trans (cg (fun t => t ◇ ((((q10 ◇ (q10 ◇ q9)) ◇ q9) ◇ q9) ◇ q9)) (cg (fun t => t ◇ q9) (apc1 q10 q9)))).trans (cg (fun t => (q9 ◇ q9) ◇ t) (cg (fun t => t ◇ q9) (apc1 q10 q9)))).symm).trans (((cg (fun t => t ◇ ((((q10 ◇ (q10 ◇ q9)) ◇ q9) ◇ (((q10 ◇ (q10 ◇ q9)) ◇ q9) ◇ q9)) ◇ q9)) (cg (fun t => t ◇ q9) (cg (fun t => ((q10 ◇ (q10 ◇ q9)) ◇ q9) ◇ t) (apc1 q10 q9)))).symm).trans (apc3 ((q10 ◇ (q10 ◇ q9)) ◇ q9) q9))
  have apc6 : forall (q11 q12 q13:G), (q12 ◇ (q11 ◇ (q12 ◇ q12))) = q11:=by
    intro q11 q12 q13
    exact ((cg (fun t => q12 ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q12) (apc1 q13 q12)))).symm).trans (((cg (fun t => q12 ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => ((q13 ◇ (q13 ◇ q12)) ◇ q12) ◇ t) (apc1 q13 q12))))).symm).trans ((h q11 q12 ((q13 ◇ (q13 ◇ q12)) ◇ q12)).symm))
  have apc7 : forall (q14 q15 q16:G), (((q14 ◇ (q14 ◇ q15)) ◇ q15) ◇ (q16 ◇ q15)) = q16:=by
    intro q14 q15 q16
    exact ((cg (fun t => ((q14 ◇ (q14 ◇ q15)) ◇ q15) ◇ t) (cg (fun t => q16 ◇ t) (apc3 q14 q15))).symm).trans (apc6 q16 ((q14 ◇ (q14 ◇ q15)) ◇ q15) q14)
  have apc8 : forall (q17 q18:G), (q17 ◇ q17) = q17:=by
    intro q17 q18
    exact ((cg (fun t => t ◇ q17) (apc1 q18 q17)).symm).trans (((cg (fun t => t ◇ q17) (cg (fun t => t ◇ q17) (apc7 q18 q17 ((q18 ◇ (q18 ◇ q17)) ◇ q17)))).symm).trans (apc1 ((q18 ◇ (q18 ◇ q17)) ◇ q17) q17))
  have apc11 : forall (q19 q20:G), ((q19 ◇ (q19 ◇ q20)) ◇ q20) = q20:=by
    intro q19 q20
    exact ((apc6 ((q19 ◇ (q19 ◇ q20)) ◇ q20) ((q19 ◇ (q19 ◇ q20)) ◇ q20) q19).symm).trans (apc0 q19 q20 ((q19 ◇ (q19 ◇ q20)) ◇ q20))
  have apc12 : forall (q21 q22:G), (q21 ◇ (q22 ◇ q21)) = q22:=by
    intro q21 q22
    exact ((cg (fun t => t ◇ (q22 ◇ q21)) (apc8 q21 (q21 ◇ q21))).symm).trans (((cg (fun t => (q21 ◇ q21) ◇ t) (cg (fun t => q22 ◇ t) (apc4 q21 q21))).symm).trans (apc6 q22 (q21 ◇ q21) q21))
  have apc13 : forall (q23 q24:G), ((q23 ◇ q24) ◇ q23) = q24:=by
    intro q23 q24
    exact ((cg (fun t => (q23 ◇ q24) ◇ t) (apc12 q24 q23)).symm).trans (apc12 (q23 ◇ q24) q24)
  have apc14 : forall (q25 q26:G), (((q26 ◇ q25) ◇ q25) ◇ q26) = q26:=by
    intro q25 q26
    exact ((cg (fun t => t ◇ q26) (cg (fun t => (q26 ◇ q25) ◇ t) (apc13 q26 q25))).symm).trans (apc11 (q26 ◇ q25) q26)
  have apc16 : forall (q27 q28:G), ((q28 ◇ q27) ◇ q27) = q28:=by
    intro q27 q28
    exact (((apc8 q28 (q28 ◇ q28)).symm).trans (((cg (fun t => q28 ◇ t) (apc14 q27 q28)).symm).trans (apc12 q28 ((q28 ◇ q27) ◇ q27)))).symm
  have apc17 : forall (q7 q8 q14 q15 q16:G), (q7 ◇ (q7 ◇ q8)) = q8:=by
    intro q7 q8 q14 q15 q16
    exact ((apc7 q7 q8 (q7 ◇ (q7 ◇ q8))).symm).trans (apc3 q7 q8)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ (y ◇ x)) ◇ z) ◇ z):=((cg (fun t => t ◇ z) (cg (fun t => t ◇ z) (apc17 y x (y ◇ (y ◇ x)) (y ◇ (y ◇ x)) (y ◇ (y ◇ x))))).trans (apc16 z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7642_to_2944 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_7642_to_2944
