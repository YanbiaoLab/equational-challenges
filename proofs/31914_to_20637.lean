-- Equation31914 → Equation20637
-- Recorded verdict: true
-- Premise: x = (x * ((x * (y * y)) * z)) * y
-- Conclusion: x = (x * y) * (((z * y) * w) * y)
-- Original submission SHA-256: 605d3d3e6a1b839d3fd8cb98cdec4664695f11c0aa0c23de530cdaaf76126455
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((x ◇ (y ◇ y)) ◇ z)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (((z ◇ y) ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ (q1 ◇ q1))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q0 ◇ (q1 ◇ q1))) (cg (fun t => q0 ◇ t) ((h q0 q1 (q0 ◇ (q1 ◇ q1))).symm))).symm).trans ((h q0 (q0 ◇ (q1 ◇ q1)) q1).symm)
  have apc1 : forall (q2 q3 q4:G), ((q3 ◇ ((q3 ◇ (q2 ◇ q2)) ◇ q4)) ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) = q3:=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => q3 ◇ t) (apc0 (q2 ◇ q2) q2))))).symm).trans ((h q3 ((q2 ◇ q2) ◇ (q2 ◇ q2)) q4).symm)
  have apc2 : forall (q5:G), (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ q5) = (q5 ◇ q5):=by
    intro q5
    exact ((cg (fun t => t ◇ q5) (cg (fun t => (q5 ◇ q5) ◇ t) (apc0 (q5 ◇ q5) q5))).symm).trans ((h (q5 ◇ q5) q5 ((q5 ◇ q5) ◇ (q5 ◇ q5))).symm)
  have apc8 : forall (q6 q7 q8 q1:G), (((q6 ◇ ((q6 ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ q7)) ◇ (q6 ◇ q1)) ◇ q8) = (q6 ◇ ((q6 ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ q7)):=by
    intro q6 q7 q8 q1
    exact ((cg (fun t => t ◇ q8) (cg (fun t => (q6 ◇ ((q6 ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ q7)) ◇ t) (cg (fun t => t ◇ q1) ((h q6 (q8 ◇ q8) q7).symm)))).symm).trans ((h (q6 ◇ ((q6 ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ q7)) q8 q1).symm)
  have apc9 : forall (q9 q10:G), (((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ ((q10 ◇ q10) ◇ q9)) = (q10 ◇ q10):=by
    intro q9 q10
    exact (((apc2 q10).symm).trans ((((cg (fun t => t ◇ q10) (apc1 (q10 ◇ q10) ((q10 ◇ q10) ◇ (q10 ◇ q10)) q9)).symm).trans (apc8 ((q10 ◇ q10) ◇ (q10 ◇ q10)) q9 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)))).trans (cg (fun t => ((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ t) (cg (fun t => t ◇ q9) (apc0 (q10 ◇ q10) q10))))).symm
  have apc10 : forall (q11 q12:G), ((q11 ◇ q11) ◇ (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ q12)) = ((q11 ◇ q11) ◇ (q11 ◇ q11)):=by
    intro q11 q12
    exact ((cg (fun t => t ◇ (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ q12)) (apc0 (q11 ◇ q11) q11)).symm).trans (apc9 q12 (q11 ◇ q11))
  have apc11 : forall (q13 q14:G), (q14 ◇ ((q14 ◇ ((q14 ◇ q14) ◇ (q14 ◇ q14))) ◇ q13)) = (q14 ◇ q14):=by
    intro q13 q14
    exact (((cg (fun t => t ◇ q14) ((h q14 (q14 ◇ q14) q13).symm)).symm).trans (apc8 q14 q13 q14 q14)).symm
  have apc12 : forall (q15:G), ((q15 ◇ q15) ◇ (q15 ◇ q15)) = q15:=by
    intro q15
    exact ((cg (fun t => (q15 ◇ q15) ◇ t) (apc11 (q15 ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) q15)).symm).trans (apc0 q15 (q15 ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))))
  have apc13 : forall (q15 q11 q12:G), ((q11 ◇ q11) ◇ (q11 ◇ q12)) = q11:=by
    intro q15 q11 q12
    exact ((cg (fun t => (q11 ◇ q11) ◇ t) (cg (fun t => t ◇ q12) (apc12 q11))).symm).trans ((apc10 q11 q12).trans (apc12 q11))
  have apc16 : forall (q16 q17 q18:G), ((q17 ◇ ((q17 ◇ q16) ◇ q18)) ◇ (q16 ◇ q16)) = q17:=by
    intro q16 q17 q18
    exact ((cg (fun t => t ◇ (q16 ◇ q16)) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => q17 ◇ t) (apc12 q16))))).symm).trans ((h q17 (q16 ◇ q16) q18).symm)
  have apc17 : forall (q19 q20 q21:G), ((q21 ◇ q21) ◇ (((q21 ◇ q19) ◇ q20) ◇ ((q21 ◇ q19) ◇ q20))) = q21:=by
    intro q19 q20 q21
    exact ((cg (fun t => t ◇ (((q21 ◇ q19) ◇ q20) ◇ ((q21 ◇ q19) ◇ q20))) (cg (fun t => q21 ◇ t) (apc16 q19 q21 q20))).symm).trans (apc16 ((q21 ◇ q19) ◇ q20) q21 (q19 ◇ q19))
  have apc20 : forall (q22 q23 q24 q25:G), (q24 ◇ ((q24 ◇ q22) ◇ q23)) = (q24 ◇ q24):=by
    intro q22 q23 q24 q25
    exact (((cg (fun t => t ◇ ((((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23)) ◇ (((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23)))) (apc13 ((q24 ◇ q24) ◇ (q24 ◇ q25)) q24 q25)).trans (cg (fun t => q24 ◇ t) (apc13 ((((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23)) ◇ (((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23))) ((q24 ◇ q22) ◇ q23) ((q24 ◇ q22) ◇ q23)))).symm).trans (((cg (fun t => t ◇ ((((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23)) ◇ (((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23)))) (cg (fun t => (q24 ◇ q24) ◇ t) (cg (fun t => t ◇ q25) (apc17 q22 q23 q24)))).symm).trans (apc16 (((q24 ◇ q22) ◇ q23) ◇ ((q24 ◇ q22) ◇ q23)) (q24 ◇ q24) q25))
  have apc23 : forall (q26 q27:G), ((q26 ◇ q26) ◇ q27) = q26:=by
    intro q26 q27
    exact ((cg (fun t => t ◇ q27) (apc20 (q27 ◇ q27) q26 q26 q26)).symm).trans ((h q26 q27 q26).symm)
  have apc25 : forall (q28 q29:G), (q28 ◇ q29) = (q28 ◇ q28):=by
    intro q28 q29
    exact ((cg (fun t => t ◇ q29) (apc17 q28 (q29 ◇ q29) q28)).symm).trans ((h (q28 ◇ q28) q29 ((q28 ◇ q28) ◇ (q29 ◇ q29))).symm)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ (((z ◇ y) ◇ w) ◇ y)):=((cg (fun t => t ◇ (((z ◇ y) ◇ w) ◇ y)) (apc25 x y)).trans (apc23 x (((z ◇ y) ◇ w) ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31914_to_20637 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31914_to_20637
