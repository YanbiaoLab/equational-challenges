-- Equation34895 → Equation2303
-- Recorded verdict: true
-- Premise: x = ((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x
-- Conclusion: x = (y ◇ (x ◇ (y ◇ y))) ◇ x
-- Original submission SHA-256: b70c60fcf49d8874b8ced092901029101c9cdfbb692b34bf9b71d382120b9952
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ (y ◇ y))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x) = (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ (q3 ◇ q3)) ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) = ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q3) ((h q3 q0 q1).symm)))).symm).trans ((h ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) q2 q3).symm)
  have apc3 : forall (q4 q5:G), (((((q5 ◇ q4) ◇ q4) ◇ ((q5 ◇ q4) ◇ q4)) ◇ ((q5 ◇ q4) ◇ q4)) ◇ ((q5 ◇ q4) ◇ q4)) = ((q5 ◇ q4) ◇ q4):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ ((q5 ◇ q4) ◇ q4)) (apc2 ((q5 ◇ q4) ◇ q4) q4 q5 q5)).symm).trans ((h ((q5 ◇ q4) ◇ q4) (q5 ◇ q5) ((q5 ◇ q4) ◇ q4)).symm)
  have apc4 : forall (q6:G), ((((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ (q6 ◇ q6)) ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q6
    exact ((((cg (fun t => t ◇ ((((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ q6)) (cg (fun t => t ◇ ((((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ q6)) (cg (fun t => (q6 ◇ q6) ◇ t) (cg (fun t => t ◇ q6) (apc1 q6 (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6)))))).trans (cg (fun t => t ◇ ((((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ q6)) (cg (fun t => ((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ t) (cg (fun t => t ◇ q6) (apc1 q6 (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6)))))).trans (cg (fun t => (((q6 ◇ q6) ◇ (q6 ◇ q6)) ◇ (q6 ◇ q6)) ◇ t) (cg (fun t => t ◇ q6) (apc1 q6 (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6))))).symm).trans ((((cg (fun t => t ◇ ((((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ q6)) (cg (fun t => t ◇ ((((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ q6)) (cg (fun t => t ◇ ((((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ q6)) (cg (fun t => t ◇ q6) (apc1 q6 q6 q6))))).symm).trans (apc3 q6 ((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)))).trans (cg (fun t => t ◇ q6) (apc1 q6 (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6))))
  have apc5 : forall (q7 q8:G), (((q8 ◇ q8) ◇ (q7 ◇ q7)) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) = ((q7 ◇ q7) ◇ (q7 ◇ q7)):=by
    intro q7 q8
    exact ((cg (fun t => t ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) (cg (fun t => (q8 ◇ q8) ◇ t) (apc4 q7))).symm).trans ((h ((q7 ◇ q7) ◇ (q7 ◇ q7)) q8 (q7 ◇ q7)).symm)
  have apc7 : forall (q9 q10 q11:G), (((q11 ◇ q11) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ ((q10 ◇ q10) ◇ (q9 ◇ q9))) = ((q10 ◇ q10) ◇ (q9 ◇ q9)):=by
    intro q9 q10 q11
    exact ((cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q9 ◇ q9))) (cg (fun t => (q11 ◇ q11) ◇ t) (apc5 q9 q9))).symm).trans (((cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q9 ◇ q9))) (cg (fun t => (q11 ◇ q11) ◇ t) (cg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) (apc5 q9 q10)))).symm).trans ((h ((q10 ◇ q10) ◇ (q9 ◇ q9)) q11 ((q9 ◇ q9) ◇ (q9 ◇ q9))).symm))
  have apc8 : forall (q12 q13 q14:G), (((q14 ◇ q14) ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) ◇ (q13 ◇ q13)) = (q13 ◇ q13):=by
    intro q12 q13 q14
    exact ((cg (fun t => t ◇ (q13 ◇ q13)) (cg (fun t => (q14 ◇ q14) ◇ t) (apc7 q12 q12 q13))).symm).trans ((h (q13 ◇ q13) q14 ((q12 ◇ q12) ◇ (q12 ◇ q12))).symm)
  have apc9 : forall (q15 q16:G), (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ (q16 ◇ q16)) = (q16 ◇ q16):=by
    intro q15 q16
    exact ((cg (fun t => t ◇ (q16 ◇ q16)) (apc5 q15 q15)).symm).trans (apc8 q15 q16 (q15 ◇ q15))
  have apc10 : forall (q6 q15 q16:G), ((q6 ◇ q6) ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q6 q15 q16
    exact ((cg (fun t => t ◇ (q6 ◇ q6)) (apc9 q6 q6)).symm).trans (apc4 q6)
  have apc11 : forall (q6 q15 q16:G), ((q15 ◇ q15) ◇ (q16 ◇ q16)) = (q16 ◇ q16):=by
    intro q6 q15 q16
    exact ((cg (fun t => t ◇ (q16 ◇ q16)) (apc10 q15 ((q15 ◇ q15) ◇ (q15 ◇ q15)) ((q15 ◇ q15) ◇ (q15 ◇ q15)))).symm).trans (apc9 q15 q16)
  have apc12 : forall (q17 q18 q19:G), ((q19 ◇ q19) ◇ ((q17 ◇ q17) ◇ ((q19 ◇ q18) ◇ q18))) = ((q17 ◇ q17) ◇ ((q19 ◇ q18) ◇ q18)):=by
    intro q17 q18 q19
    exact ((cg (fun t => t ◇ ((q17 ◇ q17) ◇ ((q19 ◇ q18) ◇ q18))) (apc8 q17 q19 (q17 ◇ q17))).symm).trans (apc2 q17 q18 ((q17 ◇ q17) ◇ (q17 ◇ q17)) q19)
  have apc13 : forall (q20 q21 q22 q23:G), ((q22 ◇ q22) ◇ ((((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21)) ◇ q23) ◇ q23)) = (q23 ◇ q23):=by
    intro q20 q21 q22 q23
    exact ((((cg (fun t => (((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21)) ◇ ((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21))) ◇ t) (apc11 ((q22 ◇ q22) ◇ (q23 ◇ q23)) q22 q23)).trans (apc11 ((((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21)) ◇ ((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21))) ◇ (q23 ◇ q23)) ((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21)) q23)).symm).trans (((cg (fun t => (((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21)) ◇ ((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21))) ◇ t) (cg (fun t => (q22 ◇ q22) ◇ t) (cg (fun t => t ◇ q23) ((h q23 q20 q21).symm)))).symm).trans (apc12 q22 q23 ((q20 ◇ q20) ◇ ((q23 ◇ q21) ◇ q21))))).symm
  have apc14 : forall (q24 q25 q26:G), ((((q24 ◇ q24) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q26) ◇ q26) = (q26 ◇ q26):=by
    intro q24 q25 q26
    exact ((((cg (fun t => t ◇ ((((q24 ◇ q24) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q26) ◇ q26)) (apc11 ((q24 ◇ q24) ◇ (q26 ◇ q26)) q24 q26)).trans (apc13 q24 q25 q26 q26)).symm).trans (((cg (fun t => t ◇ ((((q24 ◇ q24) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q26) ◇ q26)) (cg (fun t => (q24 ◇ q24) ◇ t) (apc13 q24 q25 ((((q24 ◇ q24) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q26) ◇ q26) q26))).symm).trans ((h ((((q24 ◇ q24) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q26) ◇ q26) q24 ((((q24 ◇ q24) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q26) ◇ q26)).symm))).symm
  have apc17 : forall (q27 q28 q29:G), ((((q28 ◇ q27) ◇ q27) ◇ ((q28 ◇ q27) ◇ q27)) ◇ ((q29 ◇ q29) ◇ ((q28 ◇ q27) ◇ q27))) = ((q29 ◇ q29) ◇ ((q28 ◇ q27) ◇ q27)):=by
    intro q27 q28 q29
    exact ((cg (fun t => t ◇ ((q29 ◇ q29) ◇ ((q28 ◇ q27) ◇ q27))) (apc11 ((((q28 ◇ q27) ◇ q27) ◇ ((q28 ◇ q27) ◇ q27)) ◇ (((q28 ◇ q27) ◇ q27) ◇ ((q28 ◇ q27) ◇ q27))) ((q28 ◇ q27) ◇ q27) ((q28 ◇ q27) ◇ q27))).symm).trans ((((cg (fun t => ((((q28 ◇ q27) ◇ q27) ◇ ((q28 ◇ q27) ◇ q27)) ◇ (((q28 ◇ q27) ◇ q27) ◇ ((q28 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => (q29 ◇ q29) ◇ t) (apc3 q27 q28))).symm).trans (apc12 q29 ((q28 ◇ q27) ◇ q27) (((q28 ◇ q27) ◇ q27) ◇ ((q28 ◇ q27) ◇ q27)))).trans (cg (fun t => (q29 ◇ q29) ◇ t) (apc3 q27 q28)))
  have apc50 : forall (q30 q31:G), ((((((q31 ◇ q30) ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((((q31 ◇ q30) ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((q31 ◇ q30) ◇ q30))) ◇ ((((q31 ◇ q30) ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((q31 ◇ q30) ◇ q30))) = ((((q31 ◇ q30) ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((q31 ◇ q30) ◇ q30)):=by
    intro q30 q31
    exact (((cg (fun t => (((((q31 ◇ q30) ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((((q31 ◇ q30) ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) ◇ ((q31 ◇ q30) ◇ q30))) ◇ t) (apc12 ((q31 ◇ q30) ◇ q30) q30 q31)).symm).trans (apc17 ((q31 ◇ q30) ◇ q30) ((q31 ◇ q30) ◇ q30) q31)).trans (apc12 ((q31 ◇ q30) ◇ q30) q30 q31)
  have apc51 : forall (q32 q33:G), (((((q33 ◇ q32) ◇ q32) ◇ ((q33 ◇ q32) ◇ q32)) ◇ ((q33 ◇ q32) ◇ q32)) ◇ ((((q33 ◇ q32) ◇ q32) ◇ ((q33 ◇ q32) ◇ q32)) ◇ ((q33 ◇ q32) ◇ q32))) = ((((q33 ◇ q32) ◇ q32) ◇ ((q33 ◇ q32) ◇ q32)) ◇ ((q33 ◇ q32) ◇ q32)):=by
    intro q32 q33
    exact ((cg (fun t => t ◇ ((((q33 ◇ q32) ◇ q32) ◇ ((q33 ◇ q32) ◇ q32)) ◇ ((q33 ◇ q32) ◇ q32))) (apc50 q32 q33)).symm).trans (apc3 ((q33 ◇ q32) ◇ q32) ((q33 ◇ q32) ◇ q32))
  have apc53 : forall (q34 q35 q36 q37:G), ((((((q35 ◇ q34) ◇ q34) ◇ ((q35 ◇ q34) ◇ q34)) ◇ ((q35 ◇ q34) ◇ q34)) ◇ ((q36 ◇ q37) ◇ q37)) ◇ q36) = q36:=by
    intro q34 q35 q36 q37
    exact ((cg (fun t => t ◇ q36) (cg (fun t => t ◇ ((q36 ◇ q37) ◇ q37)) (apc51 q34 q35))).symm).trans ((h q36 ((((q35 ◇ q34) ◇ q34) ◇ ((q35 ◇ q34) ◇ q34)) ◇ ((q35 ◇ q34) ◇ q34)) q37).symm)
  have apc54 : forall (q38 q39:G), (((q38 ◇ q39) ◇ q39) ◇ q38) = q38:=by
    intro q38 q39
    exact ((cg (fun t => t ◇ q38) (apc53 q39 q38 ((q38 ◇ q39) ◇ q39) ((q38 ◇ q39) ◇ q39))).symm).trans ((h q38 ((((q38 ◇ q39) ◇ q39) ◇ ((q38 ◇ q39) ◇ q39)) ◇ ((q38 ◇ q39) ◇ q39)) q39).symm)
  have apc55 : forall (q40:G), (q40 ◇ (q40 ◇ q40)) = (q40 ◇ q40):=by
    intro q40
    exact ((cg (fun t => t ◇ (q40 ◇ q40)) (apc54 q40 q40)).symm).trans (apc54 (q40 ◇ q40) q40)
  have apc57 : forall (q41:G), (q41 ◇ q41) = q41:=by
    intro q41
    exact (((((cg (fun t => t ◇ q41) (cg (fun t => t ◇ q41) (cg (fun t => (q41 ◇ q41) ◇ t) (apc11 ((q41 ◇ q41) ◇ (q41 ◇ q41)) q41 q41)))).trans (cg (fun t => t ◇ q41) (cg (fun t => t ◇ q41) (apc11 ((q41 ◇ q41) ◇ (q41 ◇ q41)) q41 q41)))).trans (apc54 q41 q41)).symm).trans (((cg (fun t => t ◇ q41) (cg (fun t => t ◇ q41) (cg (fun t => (q41 ◇ q41) ◇ t) (cg (fun t => t ◇ (q41 ◇ q41)) (apc55 q41))))).symm).trans (apc14 q41 (q41 ◇ q41) q41))).symm
  have apc58 : forall (q6 q41 q15 q16:G), (q15 ◇ q16) = q16:=by
    intro q6 q41 q15 q16
    exact (((cg (fun t => t ◇ (q16 ◇ q16)) (apc57 q15)).trans (cg (fun t => q15 ◇ t) (apc57 q16))).symm).trans ((apc11 q15 q15 q16).trans (apc57 q16))
  exact (apc58 x x (y ◇ (x ◇ (y ◇ y))) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34895_to_2303 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34895_to_2303
