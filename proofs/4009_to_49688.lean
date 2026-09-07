-- Equation4009 → Equation49688
-- Recorded verdict: true
-- Premise: x * y = (z * (y * y)) * x
-- Conclusion: x * y = (x * (y * (z * y))) * z
-- Original submission SHA-256: 0d4f0ca0f345137fb867c1fa10f836b2617a933c455abed16d20ac1d20b77844
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ (y ◇ (z ◇ y))) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((z ◇ (y ◇ y)) ◇ x) = ((x ◇ (y ◇ y)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q0 ◇ (q1 ◇ q1)) ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3 q4:G), (((q4 ◇ q4) ◇ q2) ◇ q3) = (q3 ◇ q4):=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ q3) ((h (q4 ◇ q4) q2 q2).symm)).symm).trans ((h q3 q4 (q2 ◇ (q2 ◇ q2))).symm)
  have apc3 : forall (q5 q6 q7:G), (q6 ◇ q7) = (q6 ◇ q5):=by
    intro q5 q6 q7
    exact (((apc2 (q7 ◇ q7) q6 q5).symm).trans ((h q6 q7 (q5 ◇ q5)).symm)).symm
  have apc4 : forall (q8 q9 q10 q11:G), ((q11 ◇ (q10 ◇ q10)) ◇ q8) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((apc3 q8 (q11 ◇ (q10 ◇ q10)) q9).symm).trans ((h q9 q10 q11).symm)
  have apc6 : forall (q12 q13 q14:G), ((q13 ◇ (q14 ◇ q14)) ◇ q12) = (q13 ◇ q14):=by
    intro q12 q13 q14
    exact ((apc3 q12 (q13 ◇ (q14 ◇ q14)) q13).symm).trans (apc1 q13 q14)
  have apc7 : forall (q8 q9 q10 q11:G), ((q11 ◇ (q10 ◇ q8)) ◇ q9) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((cg (fun t => t ◇ q9) (cg (fun t => q11 ◇ t) (apc3 q8 q10 q10))).symm).trans ((h q9 q10 q11).symm)
  have apc10 : forall (q15 q16 q17 q18:G), ((q15 ◇ q16) ◇ q17) = (q18 ◇ q16):=by
    intro q15 q16 q17 q18
    exact (((cg (fun t => t ◇ q17) (apc6 (q18 ◇ q18) q15 q16)).symm).trans (apc6 q17 (q15 ◇ (q16 ◇ q16)) q18)).trans (apc7 q16 q18 q16 q15)
  have apc11 : forall (q19 q20 q0 q21:G), (q0 ◇ (q20 ◇ (q19 ◇ q19))) = (q0 ◇ q19):=by
    intro q19 q20 q0 q21
    exact ((((((cg (fun t => t ◇ q0) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ (q20 ◇ (q19 ◇ q19))) (apc7 q19 (q19 ◇ q19) q19 q20)))).trans (cg (fun t => t ◇ q0) (cg (fun t => q21 ◇ t) (apc2 q19 (q20 ◇ (q19 ◇ q19)) q19)))).trans (cg (fun t => t ◇ q0) (cg (fun t => q21 ◇ t) (apc7 q19 q19 q19 q20)))).trans (apc7 q19 q0 q19 q21)).symm).trans (((cg (fun t => t ◇ q0) (cg (fun t => q21 ◇ t) (apc0 (q20 ◇ (q19 ◇ q19)) q19 q20))).symm).trans ((h q0 (q20 ◇ (q19 ◇ q19)) q21).symm))).symm
  have apc16 : forall (q22 q23 q24 q25:G), ((q22 ◇ q24) ◇ q23) = (q23 ◇ q24):=by
    intro q22 q23 q24 q25
    exact ((cg (fun t => t ◇ q23) (apc7 q24 q22 q24 q25)).symm).trans (((cg (fun t => t ◇ q23) ((apc10 q25 (q24 ◇ q24) q22 q25).symm)).symm).trans ((h q23 q24 q25).symm))
  have apc17 : forall (q26 q27 q28:G), (q26 ◇ (q27 ◇ q27)) = (q26 ◇ q27):=by
    intro q26 q27 q28
    exact ((((cg (fun t => t ◇ q26) (apc16 q27 q28 q27 ((q27 ◇ q27) ◇ q28))).trans (apc16 q28 q26 q27 ((q28 ◇ q27) ◇ q26))).symm).trans ((((cg (fun t => t ◇ q26) ((h (q27 ◇ q27) q28 q28).symm)).symm).trans (apc0 q26 q27 (q28 ◇ (q28 ◇ q28)))).trans (apc16 q26 q26 (q27 ◇ q27) ((q26 ◇ (q27 ◇ q27)) ◇ q26)))).symm
  have apc20 : forall (q29 q30 q31 q32:G), (q30 ◇ q29) = (q29 ◇ q30):=by
    intro q29 q30 q31 q32
    exact ((((cg (fun t => t ◇ q29) (apc17 q31 q30 (q31 ◇ (q30 ◇ q30)))).trans (apc16 q31 q29 q30 ((q31 ◇ q30) ◇ q29))).symm).trans ((((apc11 q29 q32 (q31 ◇ (q30 ◇ q30)) q29).symm).trans ((h (q32 ◇ (q29 ◇ q29)) q30 q31).symm)).trans ((cg (fun t => t ◇ q30) (apc17 q32 q29 (q32 ◇ (q29 ◇ q29)))).trans (apc16 q32 q30 q29 ((q32 ◇ q29) ◇ q30))))).symm
  have apc21 : forall (q33 q34 q35 q36:G), (q34 ◇ q35) = (q33 ◇ q34):=by
    intro q33 q34 q35 q36
    exact (((((cg (fun t => t ◇ q33) (apc20 (q34 ◇ q34) q36 (q36 ◇ (q34 ◇ q34)) (q36 ◇ (q34 ◇ q34)))).trans (cg (fun t => t ◇ q33) (apc16 q34 q36 q34 ((q34 ◇ q34) ◇ q36)))).trans (apc16 q36 q33 q34 ((q36 ◇ q34) ◇ q33))).symm).trans ((apc4 q33 (q33 ◇ (q35 ◇ q35)) q34 q36).trans ((h q34 q35 q33).symm))).symm
  exact (apc21 z x y (x ◇ y)).trans (apc21 (x ◇ (y ◇ (z ◇ y))) z x (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4009_to_49688 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4009_to_49688
