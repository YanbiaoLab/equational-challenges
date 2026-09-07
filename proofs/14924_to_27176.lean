-- Equation14924 → Equation27176
-- Recorded verdict: true
-- Premise: x = y * (((z * y) * (x * x)) * x)
-- Conclusion: x = ((y * z) * (x * w)) * (x * x)
-- Original submission SHA-256: 3981e0be90a8c99e72d524b9fdcd8c5bf709a470bbdd67f2584fd8ec23110302
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ y) ◇ (x ◇ x)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ (x ◇ w)) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), ((((q1 ◇ q3) ◇ (q0 ◇ q0)) ◇ q0) ◇ ((q0 ◇ (q2 ◇ q2)) ◇ q2)) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (((q1 ◇ q3) ◇ (q0 ◇ q0)) ◇ q0) ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ (q2 ◇ q2)) ((h q0 q3 q1).symm)))).symm).trans ((h q2 (((q1 ◇ q3) ◇ (q0 ◇ q0)) ◇ q0) q3).symm)
  have apc1 : forall (q4 q5 q6:G), (((q4 ◇ (q5 ◇ q5)) ◇ q5) ◇ ((q5 ◇ (q6 ◇ q6)) ◇ q6)) = q6:=by
    intro q4 q5 q6
    exact ((cg (fun t => ((q4 ◇ (q5 ◇ q5)) ◇ q5) ◇ t) (cg (fun t => t ◇ q6) (cg (fun t => t ◇ (q6 ◇ q6)) (apc0 q4 q4 q5 q4)))).symm).trans ((h q6 ((q4 ◇ (q5 ◇ q5)) ◇ q5) (((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ q4)).symm)
  have apc4 : forall (q7 q8 q9:G), (q8 ◇ (((q9 ◇ q8) ◇ q7) ◇ ((q7 ◇ (q7 ◇ q7)) ◇ q7))) = ((q7 ◇ (q7 ◇ q7)) ◇ q7):=by
    intro q7 q8 q9
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ ((q7 ◇ (q7 ◇ q7)) ◇ q7)) (cg (fun t => (q9 ◇ q8) ◇ t) (apc1 q7 q7 q7)))).symm).trans ((h ((q7 ◇ (q7 ◇ q7)) ◇ q7) q8 q9).symm)
  have apc6 : forall (q10:G), ((q10 ◇ (q10 ◇ q10)) ◇ q10) = (q10 ◇ q10):=by
    intro q10
    exact (((cg (fun t => q10 ◇ t) (apc1 q10 q10 q10)).symm).trans (((cg (fun t => q10 ◇ t) (cg (fun t => t ◇ ((q10 ◇ (q10 ◇ q10)) ◇ q10)) (apc4 q10 (q10 ◇ q10) q10))).symm).trans ((h ((q10 ◇ (q10 ◇ q10)) ◇ q10) q10 q10).symm))).symm
  have apc7 : forall (q11 q12:G), (((q11 ◇ (q12 ◇ q12)) ◇ q12) ◇ (q12 ◇ q12)) = q12:=by
    intro q11 q12
    exact ((cg (fun t => ((q11 ◇ (q12 ◇ q12)) ◇ q12) ◇ t) (apc6 q12)).symm).trans (apc1 q11 q12 q12)
  have apc8 : forall (q13:G), (q13 ◇ (q13 ◇ q13)) = q13:=by
    intro q13
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q13) (apc7 q13 q13))).symm).trans ((h q13 q13 (q13 ◇ (q13 ◇ q13))).symm)
  have apc9 : forall (q14:G), ((q14 ◇ q14) ◇ (q14 ◇ q14)) = q14:=by
    intro q14
    exact ((cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => t ◇ q14) (apc7 q14 q14))).symm).trans (apc7 ((q14 ◇ (q14 ◇ q14)) ◇ q14) q14)
  have apc11 : forall (q15 q16:G), (((q16 ◇ q15) ◇ (q15 ◇ q15)) ◇ q15) = (q15 ◇ q15):=by
    intro q15 q16
    exact ((cg (fun t => ((q16 ◇ q15) ◇ (q15 ◇ q15)) ◇ t) (apc9 q15)).symm).trans (((cg (fun t => t ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) (cg (fun t => t ◇ (q15 ◇ q15)) (cg (fun t => q16 ◇ t) (apc9 q15)))).symm).trans (apc7 q16 (q15 ◇ q15)))
  have apc13 : forall (q17 q18 q19:G), (((q18 ◇ ((q17 ◇ q19) ◇ (q17 ◇ q19))) ◇ (q17 ◇ q19)) ◇ (q19 ◇ q19)) = q19:=by
    intro q17 q18 q19
    exact ((cg (fun t => ((q18 ◇ ((q17 ◇ q19) ◇ (q17 ◇ q19))) ◇ (q17 ◇ q19)) ◇ t) (apc11 q19 q17)).symm).trans (apc1 q18 (q17 ◇ q19) q19)
  have apc15 : forall (q20 q21:G), ((q20 ◇ q21) ◇ (q21 ◇ q21)) = q21:=by
    intro q20 q21
    exact ((cg (fun t => (q20 ◇ q21) ◇ t) (cg (fun t => t ◇ q21) (apc13 q20 q20 q21))).symm).trans ((h q21 (q20 ◇ q21) (q20 ◇ ((q20 ◇ q21) ◇ (q20 ◇ q21)))).symm)
  have apc16 : forall (q22 q23 q24 q25:G), ((q22 ◇ q23) ◇ (q22 ◇ q23)) = (q24 ◇ (q22 ◇ q23)):=by
    intro q22 q23 q24 q25
    exact ((((cg (fun t => q24 ◇ t) (cg (fun t => ((q25 ◇ q24) ◇ (q22 ◇ q23)) ◇ t) (cg (fun t => t ◇ (q22 ◇ q23)) (apc8 (q22 ◇ q23))))).trans (cg (fun t => q24 ◇ t) (apc15 (q25 ◇ q24) (q22 ◇ q23)))).symm).trans ((((cg (fun t => q24 ◇ t) (cg (fun t => t ◇ (((q22 ◇ q23) ◇ ((q22 ◇ q23) ◇ (q22 ◇ q23))) ◇ (q22 ◇ q23))) (cg (fun t => (q25 ◇ q24) ◇ t) (apc0 (q22 ◇ q23) q22 (q22 ◇ q23) q23)))).symm).trans ((h (((q22 ◇ q23) ◇ ((q22 ◇ q23) ◇ (q22 ◇ q23))) ◇ (q22 ◇ q23)) q24 q25).symm)).trans (cg (fun t => t ◇ (q22 ◇ q23)) (apc8 (q22 ◇ q23))))).symm
  have apc18 : forall (q26 q27 q28:G), (((q26 ◇ (q27 ◇ q27)) ◇ q27) ◇ (q28 ◇ q28)) = q28:=by
    intro q26 q27 q28
    exact ((cg (fun t => ((q26 ◇ (q27 ◇ q27)) ◇ q27) ◇ t) (cg (fun t => t ◇ q28) (apc15 q28 q28))).symm).trans (((cg (fun t => ((q26 ◇ (q27 ◇ q27)) ◇ q27) ◇ t) (cg (fun t => t ◇ q28) ((apc16 q28 q28 q27 q26).symm))).symm).trans (apc1 q26 q27 q28))
  have apc19 : forall (q29 q30 q31:G), (((q29 ◇ q30) ◇ (q29 ◇ q30)) ◇ (q31 ◇ q31)) = q31:=by
    intro q29 q30 q31
    exact ((cg (fun t => t ◇ (q31 ◇ q31)) ((apc16 q29 q30 (q29 ◇ ((q29 ◇ q30) ◇ (q29 ◇ q30))) q29).symm)).symm).trans (apc18 q29 (q29 ◇ q30) q31)
  have apc21 : forall (q32 q33 q34:G), ((q32 ◇ q33) ◇ (q34 ◇ q34)) = q34:=by
    intro q32 q33 q34
    exact ((cg (fun t => t ◇ (q34 ◇ q34)) (apc19 q32 q33 (q32 ◇ q33))).symm).trans (apc19 (q32 ◇ q33) (q32 ◇ q33) q34)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ z) ◇ (x ◇ w)) ◇ (x ◇ x)):=(apc21 (y ◇ z) (x ◇ w) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14924_to_27176 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14924_to_27176
