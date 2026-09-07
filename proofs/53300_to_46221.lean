-- Equation53300 → Equation46221
-- Recorded verdict: true
-- Premise: x * y = (((y * x) * y) * z) * x
-- Conclusion: x * y = (x * z) * (y * (w * y))
-- Original submission SHA-256: 2b3ffc86c10678b0c5568cf4fbcbce7af4bb24f731beb3d76479ba5ea6f66c76
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((y ◇ x) ◇ y) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ z) ◇ (y ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (q0 ◇ (q0 ◇ q1)) = ((q1 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q0) ((h q1 q0 (q0 ◇ q1)).symm)).symm).trans ((h q0 (q0 ◇ q1) q1).symm)).symm
  have apc4 : forall (q2 q3 q4:G), (((((q2 ◇ q3) ◇ q3) ◇ q3) ◇ q4) ◇ (q3 ◇ q2)) = ((q3 ◇ q2) ◇ q3):=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ (q3 ◇ q2)) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q3) (apc0 q3 q2)))).symm).trans ((h (q3 ◇ q2) q3 q4).symm)
  have apc5 : forall (x y z:G), ((((y ◇ x) ◇ y) ◇ z) ◇ x) = ((((y ◇ x) ◇ y) ◇ x) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc7 : forall (q5 q6:G), ((((q6 ◇ q5) ◇ q6) ◇ q5) ◇ q5) = (q5 ◇ q6):=by
    intro q5 q6
    exact ((apc5 q5 q6 q5).symm).trans ((h q5 q6 q5).symm)
  have apc8 : forall (q7 q8:G), (((q8 ◇ q7) ◇ q8) ◇ (q8 ◇ (q7 ◇ q8))) = ((q8 ◇ (q7 ◇ q8)) ◇ q8):=by
    intro q7 q8
    exact ((cg (fun t => t ◇ (q8 ◇ (q7 ◇ q8))) (apc4 q7 q8 q8)).symm).trans (apc4 (q7 ◇ q8) q8 (q8 ◇ q7))
  have apc9 : forall (q9 q10:G), (((q10 ◇ (q9 ◇ q10)) ◇ q10) ◇ q9) = (q9 ◇ q10):=by
    intro q9 q10
    exact ((cg (fun t => t ◇ q9) (apc8 q9 q10)).symm).trans ((h q9 q10 (q10 ◇ (q9 ◇ q10))).symm)
  have apc10 : forall (q11 q12:G), ((q12 ◇ q11) ◇ (q12 ◇ q11)) = ((q12 ◇ q11) ◇ q11):=by
    intro q11 q12
    exact ((cg (fun t => t ◇ (q12 ◇ q11)) (apc9 q12 q11)).symm).trans ((h (q12 ◇ q11) q11 q12).symm)
  have apc12 : forall (q13 q14:G), ((q14 ◇ q13) ◇ q14) = ((q14 ◇ q13) ◇ q13):=by
    intro q13 q14
    exact ((((cg (fun t => (q14 ◇ q13) ◇ t) (apc7 q14 q13)).trans (apc10 q13 q14)).symm).trans ((((cg (fun t => t ◇ ((((q13 ◇ q14) ◇ q13) ◇ q14) ◇ q14)) (apc7 q14 q13)).symm).trans (apc10 q14 (((q13 ◇ q14) ◇ q13) ◇ q14))).trans (cg (fun t => t ◇ q14) (apc7 q14 q13)))).symm
  have apc13 : forall (q5 q6 q13 q14:G), ((((q6 ◇ q5) ◇ q5) ◇ q5) ◇ q5) = (q5 ◇ q6):=by
    intro q5 q6 q13 q14
    exact ((cg (fun t => t ◇ q5) (cg (fun t => t ◇ q5) (apc12 q5 q6))).symm).trans (apc7 q5 q6)
  have apc17 : forall (q2 q15 q3:G), (((q2 ◇ ((q3 ◇ q15) ◇ q15)) ◇ ((q3 ◇ q15) ◇ q15)) ◇ q15) = (q15 ◇ q3):=by
    intro q2 q15 q3
    exact (((cg (fun t => t ◇ q15) (cg (fun t => t ◇ ((q3 ◇ q15) ◇ q3)) (cg (fun t => q2 ◇ t) (apc12 q15 q3)))).trans (cg (fun t => t ◇ q15) (cg (fun t => (q2 ◇ ((q3 ◇ q15) ◇ q15)) ◇ t) (apc12 q15 q3)))).symm).trans (((cg (fun t => t ◇ q15) (apc0 ((q3 ◇ q15) ◇ q3) q2)).symm).trans ((h q15 q3 (((q3 ◇ q15) ◇ q3) ◇ q2)).symm))
  have apc18 : forall (q16 q17:G), ((q16 ◇ q17) ◇ q16) = (q16 ◇ q17):=by
    intro q16 q17
    exact (((cg (fun t => t ◇ q16) (apc12 q16 ((q17 ◇ q16) ◇ q16))).trans (cg (fun t => t ◇ q16) (apc13 q16 q17 ((((q17 ◇ q16) ◇ q16) ◇ q16) ◇ q16) ((((q17 ◇ q16) ◇ q16) ◇ q16) ◇ q16)))).symm).trans (((cg (fun t => t ◇ q16) (cg (fun t => t ◇ ((q17 ◇ q16) ◇ q16)) (apc10 q16 (q17 ◇ q16)))).symm).trans (apc17 ((q17 ◇ q16) ◇ q16) q16 q17))
  have apc19 : forall (q16 q17 q13 q14:G), ((q14 ◇ q13) ◇ q13) = (q14 ◇ q13):=by
    intro q16 q17 q13 q14
    exact (((apc18 q14 q13).symm).trans (apc12 q13 q14)).symm
  have apc20 : forall (q11 q12 q16 q17 q13 q14:G), ((q12 ◇ q11) ◇ (q12 ◇ q11)) = (q12 ◇ q11):=by
    intro q11 q12 q16 q17 q13 q14
    exact (apc10 q11 q12).trans (apc19 ((q12 ◇ q11) ◇ q11) ((q12 ◇ q11) ◇ q11) q11 q12)
  have apc21 : forall (q18 q19 q20:G), ((q19 ◇ q18) ◇ q20) = (q19 ◇ q18):=by
    intro q18 q19 q20
    exact (((cg (fun t => t ◇ (q19 ◇ q18)) (cg (fun t => t ◇ q20) (apc20 q18 q19 ((q19 ◇ q18) ◇ (q19 ◇ q18)) ((q19 ◇ q18) ◇ (q19 ◇ q18)) ((q19 ◇ q18) ◇ (q19 ◇ q18)) ((q19 ◇ q18) ◇ (q19 ◇ q18))))).trans (apc18 (q19 ◇ q18) q20)).symm).trans ((((cg (fun t => t ◇ (q19 ◇ q18)) (cg (fun t => t ◇ q20) (cg (fun t => t ◇ (q19 ◇ q18)) (apc20 q18 q19 q18 q18 q18 q18)))).symm).trans ((h (q19 ◇ q18) (q19 ◇ q18) q20).symm)).trans (apc20 q18 q19 ((q19 ◇ q18) ◇ (q19 ◇ q18)) ((q19 ◇ q18) ◇ (q19 ◇ q18)) ((q19 ◇ q18) ◇ (q19 ◇ q18)) ((q19 ◇ q18) ◇ (q19 ◇ q18))))
  have apc22 : forall (q0 q1 q16 q17 q13 q14:G), (q0 ◇ (q0 ◇ q1)) = (q1 ◇ q0):=by
    intro q0 q1 q16 q17 q13 q14
    exact (apc0 q0 q1).trans (apc19 ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0) q0 q1)
  have apc24 : forall (q21 q22 q23:G), (q21 ◇ (q23 ◇ q22)) = (q22 ◇ q23):=by
    intro q21 q22 q23
    exact (((cg (fun t => t ◇ q22) (cg (fun t => q21 ◇ t) (apc21 q22 q23 q23))).trans (apc21 (q23 ◇ q22) q21 q22)).symm).trans (((cg (fun t => t ◇ q22) (apc22 ((q23 ◇ q22) ◇ q23) q21 q21 q21 q21 q21)).symm).trans ((h q22 q23 (((q23 ◇ q22) ◇ q23) ◇ q21)).symm))
  have apc25 : forall (q24 q25:G), (q25 ◇ q24) = (q24 ◇ q25):=by
    intro q24 q25
    exact (((cg (fun t => t ◇ q24) (apc21 q24 q25 q25)).trans (apc21 q24 q25 q24)).symm).trans (((cg (fun t => t ◇ q24) (apc18 (q25 ◇ q24) q25)).symm).trans ((h q24 q25 (q25 ◇ q24)).symm))
  have apc30 : forall (q26 q27 q28 q29:G), (q28 ◇ q29) = (q26 ◇ q27):=by
    intro q26 q27 q28 q29
    exact ((((apc24 (q29 ◇ q28) q26 q27).symm).trans (apc21 q28 q29 (q27 ◇ q26))).trans (apc25 q28 q29)).symm
  exact (apc30 (x ◇ y) ((x ◇ z) ◇ (y ◇ (w ◇ y))) x y).trans ((apc30 (x ◇ y) ((x ◇ z) ◇ (y ◇ (w ◇ y))) (x ◇ z) (y ◇ (w ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53300_to_46221 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53300_to_46221
