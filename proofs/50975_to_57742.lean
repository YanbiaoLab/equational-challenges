-- Equation50975 → Equation57742
-- Recorded verdict: true
-- Premise: x * y = (z * ((z * y) * x)) * x
-- Conclusion: x * (y * y) = ((y * z) * w) * u
-- Original submission SHA-256: d9e52fd7742c9e2b6df535da1c742ded230165a1c3d15a485df1a7de70531506
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ ((z ◇ y) ◇ x)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ y) = ((y ◇ z) ◇ w) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ q0) ◇ q1)) = ((q2 ◇ (q1 ◇ q0)) ◇ q1):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q1) (cg (fun t => q2 ◇ t) ((h q1 q0 q2).symm))).symm).trans ((h q1 ((q2 ◇ q0) ◇ q1) q2).symm)).symm
  have apc1 : forall (q3 q4:G), (((q3 ◇ (q3 ◇ q4)) ◇ q3) ◇ q3) = (q3 ◇ q4):=by
    intro q3 q4
    exact ((cg (fun t => t ◇ q3) (apc0 q4 q3 q3)).symm).trans ((h q3 q4 q3).symm)
  have apc2 : forall (q5 q6:G), (((q6 ◇ (q6 ◇ q5)) ◇ (q6 ◇ q6)) ◇ q6) = (q6 ◇ (q6 ◇ q5)):=by
    intro q5 q6
    exact (((cg (fun t => q6 ◇ t) (apc1 q6 q5)).symm).trans (apc0 q6 q6 (q6 ◇ (q6 ◇ q5)))).symm
  have apc3 : forall (q7 q8:G), (((q8 ◇ (q8 ◇ q7)) ◇ (q8 ◇ q7)) ◇ q8) = (q8 ◇ q8):=by
    intro q7 q8
    exact ((cg (fun t => t ◇ q8) (cg (fun t => (q8 ◇ (q8 ◇ q7)) ◇ t) (apc1 q8 q7))).symm).trans ((h q8 q8 (q8 ◇ (q8 ◇ q7))).symm)
  have apc4 : forall (q9:G), (q9 ◇ (q9 ◇ q9)) = (q9 ◇ q9):=by
    intro q9
    exact (((apc3 q9 q9).symm).trans (apc2 q9 q9)).symm
  have apc7 : forall (q10 q11:G), ((q11 ◇ ((q11 ◇ q11) ◇ q10)) ◇ q10) = (q10 ◇ (q11 ◇ q11)):=by
    intro q10 q11
    exact ((cg (fun t => t ◇ q10) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q10) (apc4 q11)))).symm).trans ((h q10 (q11 ◇ q11) q11).symm)
  have apc8 : forall (q12 q13:G), (q12 ◇ (q13 ◇ q13)) = (q12 ◇ q13):=by
    intro q12 q13
    exact ((apc7 q12 q13).symm).trans ((h q12 q13 q13).symm)
  have apc9 : forall (q5 q6 q12 q13:G), (q6 ◇ (q6 ◇ q5)) = (q6 ◇ q5):=by
    intro q5 q6 q12 q13
    exact (((apc1 q6 q5).symm).trans (((cg (fun t => t ◇ q6) (apc8 (q6 ◇ (q6 ◇ q5)) q6)).symm).trans (apc2 q5 q6))).symm
  have apc10 : forall (q0 q14 q1 q15:G), (((q14 ◇ ((q14 ◇ q0) ◇ q15)) ◇ ((q15 ◇ q0) ◇ q1)) ◇ q1) = (q1 ◇ q15):=by
    intro q0 q14 q1 q15
    exact ((cg (fun t => t ◇ q1) (cg (fun t => (q14 ◇ ((q14 ◇ q0) ◇ q15)) ◇ t) (cg (fun t => t ◇ q1) ((h q15 q0 q14).symm)))).symm).trans ((h q1 q15 (q14 ◇ ((q14 ◇ q0) ◇ q15))).symm)
  have apc12 : forall (q16 q17 q18 q19:G), ((q17 ◇ q17) ◇ q16) = (q17 ◇ q16):=by
    intro q16 q17 q18 q19
    exact (((apc10 q18 q19 (q17 ◇ q17) q16).symm).trans (apc8 ((q19 ◇ ((q19 ◇ q18) ◇ q16)) ◇ ((q16 ◇ q18) ◇ (q17 ◇ q17))) q17)).trans ((cg (fun t => t ◇ q17) (cg (fun t => (q19 ◇ ((q19 ◇ q18) ◇ q16)) ◇ t) (apc8 (q16 ◇ q18) q17))).trans (apc10 q18 q19 q17 q16))
  have apc13 : forall (q20 q21:G), ((q21 ◇ q20) ◇ q20) = (q20 ◇ q21):=by
    intro q20 q21
    exact ((cg (fun t => t ◇ q20) (apc9 q20 q21 (q21 ◇ (q21 ◇ q20)) (q21 ◇ (q21 ◇ q20)))).symm).trans (((cg (fun t => t ◇ q20) (cg (fun t => q21 ◇ t) (apc12 q20 q21 q20 q20))).symm).trans ((h q20 q21 q21).symm))
  have apc15 : forall (q22 q23:G), ((q23 ◇ q22) ◇ q23) = (q23 ◇ q23):=by
    intro q22 q23
    exact (((cg (fun t => t ◇ q23) (apc13 q23 (q23 ◇ q22))).trans (cg (fun t => t ◇ q23) (apc9 q22 q23 (q23 ◇ (q23 ◇ q22)) (q23 ◇ (q23 ◇ q22))))).symm).trans (((cg (fun t => t ◇ q23) (apc13 ((q23 ◇ q22) ◇ q23) q23)).symm).trans (apc10 q22 q23 q23 q23))
  have apc18 : forall (q24 q25 q26:G), (q25 ◇ (q26 ◇ q24)) = (q25 ◇ q26):=by
    intro q24 q25 q26
    exact (((apc12 q25 ((q26 ◇ q24) ◇ q25) ((((q26 ◇ q24) ◇ q25) ◇ ((q26 ◇ q24) ◇ q25)) ◇ q25) ((((q26 ◇ q24) ◇ q25) ◇ ((q26 ◇ q24) ◇ q25)) ◇ q25)).trans (apc13 q25 (q26 ◇ q24))).symm).trans (((cg (fun t => t ◇ q25) (apc15 ((((q26 ◇ q24) ◇ q25) ◇ q24) ◇ q26) ((q26 ◇ q24) ◇ q25))).symm).trans (apc10 q24 ((q26 ◇ q24) ◇ q25) q25 q26))
  have apc21 : forall (q0 q14 q1 q15 q24 q25 q26:G), ((q14 ◇ q15) ◇ q1) = (q1 ◇ q15):=by
    intro q0 q14 q1 q15 q24 q25 q26
    exact ((cg (fun t => t ◇ q1) (apc12 q15 q14 ((q14 ◇ q14) ◇ q15) ((q14 ◇ q14) ◇ q15))).symm).trans ((((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q15 ◇ q0) ◇ q1)) (apc18 q15 q14 (q14 ◇ q0)))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q15 ◇ q0) ◇ q1)) (apc18 q0 q14 q14)))).trans (cg (fun t => t ◇ q1) (apc18 q1 (q14 ◇ q14) (q15 ◇ q0)))).trans (cg (fun t => t ◇ q1) (apc18 q0 (q14 ◇ q14) q15))).symm).trans (apc10 q0 q14 q1 q15))
  have apc22 : forall (q7 q8 q5 q6 q12 q13:G), (q8 ◇ q8) = (q8 ◇ q7):=by
    intro q7 q8 q5 q6 q12 q13
    exact (((((cg (fun t => t ◇ q8) (apc18 q7 (q8 ◇ q7) q8)).trans (cg (fun t => t ◇ q8) (apc21 ((q8 ◇ q7) ◇ q8) q8 q8 q7 ((q8 ◇ q7) ◇ q8) ((q8 ◇ q7) ◇ q8) ((q8 ◇ q7) ◇ q8)))).trans (apc21 ((q8 ◇ q7) ◇ q8) q8 q8 q7 ((q8 ◇ q7) ◇ q8) ((q8 ◇ q7) ◇ q8) ((q8 ◇ q7) ◇ q8))).symm).trans (((cg (fun t => t ◇ q8) (cg (fun t => t ◇ (q8 ◇ q7)) (apc9 q7 q8 (q8 ◇ (q8 ◇ q7)) (q8 ◇ (q8 ◇ q7))))).symm).trans (apc3 q7 q8))).symm
  have apc23 : forall (q27 q28 q29:G), (q29 ◇ q27) = (q28 ◇ q28):=by
    intro q27 q28 q29
    exact (((((cg (fun t => t ◇ (q29 ◇ q28)) (cg (fun t => q29 ◇ t) (apc21 ((q29 ◇ q28) ◇ q27) q29 q27 q28 ((q29 ◇ q28) ◇ q27) ((q29 ◇ q28) ◇ q27) ((q29 ◇ q28) ◇ q27)))).trans (cg (fun t => t ◇ (q29 ◇ q28)) (apc18 q28 q29 q27))).trans (apc18 q28 (q29 ◇ q27) q29)).trans (apc21 ((q29 ◇ q27) ◇ q29) q29 q29 q27 ((q29 ◇ q27) ◇ q29) ((q29 ◇ q27) ◇ q29) ((q29 ◇ q27) ◇ q29))).symm).trans ((((cg (fun t => t ◇ (q29 ◇ q28)) (cg (fun t => q29 ◇ t) (apc22 q27 (q29 ◇ q28) q27 q27 q27 q27))).symm).trans ((h (q29 ◇ q28) q28 q29).symm)).trans (apc21 ((q29 ◇ q28) ◇ q28) q29 q28 q28 ((q29 ◇ q28) ◇ q28) ((q29 ◇ q28) ◇ q28) ((q29 ◇ q28) ◇ q28)))
  exact (apc23 (y ◇ y) (x ◇ (y ◇ y)) x).trans ((apc23 u (x ◇ (y ◇ y)) ((y ◇ z) ◇ w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50975_to_57742 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50975_to_57742
