-- Equation47394 → Equation405
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((y * y) * x)
-- Conclusion: x * y = (z * z) * w
-- Original submission SHA-256: a014b9f779d8ad74511f0000b372c5a8d9d6610e46b08d39ef9cd38ae0e8bfc6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ ((y ◇ y) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ q1) = ((q2 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q2 ◇ q1) ◇ t) ((h q0 q1 q1).symm)).symm).trans ((h ((q1 ◇ q1) ◇ q0) q1 q2).symm)).symm
  have apc1 : forall (q3:G), (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) = (q3 ◇ q3):=by
    intro q3
    exact (apc0 (q3 ◇ q3) q3 q3).trans ((h q3 q3 q3).symm)
  have apc2 : forall (q4 q5:G), ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ q4)) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ ((q5 ◇ q5) ◇ q4)) (apc1 q5)).symm).trans ((h q4 q5 ((q5 ◇ q5) ◇ (q5 ◇ q5))).symm)
  have apc3 : forall (q6 q7:G), ((q7 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) = (q6 ◇ q6):=by
    intro q6 q7
    exact (((apc1 q6).symm).trans (apc0 (q6 ◇ q6) q6 q7)).symm
  have apc4 : forall (q8:G), ((q8 ◇ q8) ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q8
    exact (((cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => t ◇ ((q8 ◇ q8) ◇ q8)) (apc3 q8 (q8 ◇ q8)))).trans (cg (fun t => (q8 ◇ q8) ◇ t) (apc2 q8 q8))).symm).trans ((((cg (fun t => t ◇ ((((q8 ◇ q8) ◇ q8) ◇ ((q8 ◇ q8) ◇ q8)) ◇ ((q8 ◇ q8) ◇ q8))) (apc3 q8 q8)).symm).trans (apc3 ((q8 ◇ q8) ◇ q8) (q8 ◇ q8))).trans (apc3 q8 (q8 ◇ q8)))
  have apc5 : forall (x y z:G), ((z ◇ y) ◇ ((y ◇ y) ◇ x)) = ((x ◇ y) ◇ ((y ◇ y) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc6 : forall (q3 q8:G), ((q3 ◇ q3) ◇ q3) = (q3 ◇ q3):=by
    intro q3 q8
    exact ((cg (fun t => t ◇ q3) (apc4 q3)).symm).trans (apc1 q3)
  have apc7 : forall (q9 q10:G), ((q10 ◇ q9) ◇ (q9 ◇ q9)) = (q9 ◇ q9):=by
    intro q9 q10
    exact ((cg (fun t => (q10 ◇ q9) ◇ t) (apc6 q9 q9)).symm).trans ((h q9 q9 q10).symm)
  have apc8 : forall (x y z q4 q5:G), ((q4 ◇ q5) ◇ ((q5 ◇ q5) ◇ q4)) = (q4 ◇ q5):=by
    intro x y z q4 q5
    exact ((apc5 q4 q5 q5).symm).trans (apc2 q4 q5)
  have apc10 : forall (q11 q12:G), ((q11 ◇ q11) ◇ ((q11 ◇ q11) ◇ q12)) = (q12 ◇ (q11 ◇ q11)):=by
    intro q11 q12
    exact ((cg (fun t => (q11 ◇ q11) ◇ t) (cg (fun t => t ◇ q12) (apc7 q11 q11))).symm).trans (((cg (fun t => t ◇ (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ q12)) (apc4 q11)).symm).trans ((h q12 (q11 ◇ q11) (q11 ◇ q11)).symm))
  have apc11 : forall (q13 q14:G), (q13 ◇ (q14 ◇ q14)) = (q13 ◇ q14):=by
    intro q13 q14
    exact ((apc10 q14 q13).symm).trans ((h q13 q14 q14).symm)
  have apc12 : forall (q13 q14 q9 q10:G), ((q10 ◇ q9) ◇ q9) = (q9 ◇ q9):=by
    intro q13 q14 q9 q10
    exact ((apc11 (q10 ◇ q9) q9).symm).trans (apc7 q9 q10)
  have apc15 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q0 ◇ q1)) = ((q0 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q1 q0)
  have apc17 : forall (q15 q16 q17:G), ((q15 ◇ q16) ◇ (q15 ◇ q16)) = (q16 ◇ q16):=by
    intro q15 q16 q17
    exact (((apc11 (q17 ◇ q16) (q15 ◇ q16)).trans (apc15 q15 q16 q17)).symm).trans ((((cg (fun t => (q17 ◇ q16) ◇ t) (apc15 q15 q16 q16)).symm).trans ((h (q15 ◇ q16) q16 q17).symm)).trans (apc12 ((q15 ◇ q16) ◇ q16) ((q15 ◇ q16) ◇ q16) q16 q15))
  have apc18 : forall (q18 q19:G), (q19 ◇ q19) = (q18 ◇ q18):=by
    intro q18 q19
    exact (((cg (fun t => (q18 ◇ q19) ◇ t) (apc8 ((q18 ◇ q19) ◇ ((q19 ◇ q19) ◇ q18)) ((q18 ◇ q19) ◇ ((q19 ◇ q19) ◇ q18)) ((q18 ◇ q19) ◇ ((q19 ◇ q19) ◇ q18)) q18 q19)).trans (apc17 q18 q19 ((q18 ◇ q19) ◇ (q18 ◇ q19)))).symm).trans ((((cg (fun t => t ◇ ((q18 ◇ q19) ◇ ((q19 ◇ q19) ◇ q18))) (apc8 q18 q18 q18 q18 q19)).symm).trans (apc17 (q18 ◇ q19) ((q19 ◇ q19) ◇ q18) q18)).trans (apc17 (q19 ◇ q19) q18 (((q19 ◇ q19) ◇ q18) ◇ ((q19 ◇ q19) ◇ q18))))
  have apc20 : forall (q20 q21 q22:G), ((q22 ◇ q21) ◇ q20) = (q21 ◇ q21):=by
    intro q20 q21 q22
    exact ((apc11 (q22 ◇ q21) q20).symm).trans ((((cg (fun t => (q22 ◇ q21) ◇ t) (apc18 q20 (q21 ◇ q21))).symm).trans ((h (q21 ◇ q21) q21 q22).symm)).trans (apc12 ((q21 ◇ q21) ◇ q21) ((q21 ◇ q21) ◇ q21) q21 q21))
  have apc21 : forall (q3 q23 q24:G), (q23 ◇ q23) = (q3 ◇ q23):=by
    intro q3 q23 q24
    exact (((((((cg (fun t => t ◇ (q23 ◇ ((q23 ◇ q23) ◇ q3))) (cg (fun t => q24 ◇ t) (apc20 q3 q23 q23))).trans (cg (fun t => (q24 ◇ (q23 ◇ q23)) ◇ t) (cg (fun t => q23 ◇ t) (apc20 q3 q23 q23)))).trans (cg (fun t => t ◇ (q23 ◇ (q23 ◇ q23))) (apc11 q24 q23))).trans (cg (fun t => (q24 ◇ q23) ◇ t) (apc11 q23 q23))).trans (apc11 (q24 ◇ q23) q23)).trans (apc20 q23 q23 q24)).symm).trans (((apc0 q23 ((q23 ◇ q23) ◇ q3) q24).symm).trans ((h q3 q23 (((q23 ◇ q23) ◇ q3) ◇ ((q23 ◇ q23) ◇ q3))).symm))
  have apc22 : forall (q25 q26 q27:G), (q26 ◇ q27) = (q25 ◇ q27):=by
    intro q25 q26 q27
    exact (((apc21 q25 q27 q25).symm).trans (apc21 q26 q27 q25)).symm
  have apc23 : forall (q28 q29 q30:G), (q29 ◇ q30) = (q29 ◇ q28):=by
    intro q28 q29 q30
    exact (((apc11 q29 q28).symm).trans (((cg (fun t => q29 ◇ t) (apc18 q28 q30)).symm).trans (apc11 q29 q30))).symm
  have apc24 : forall (q31 q32 q33 q34:G), (q33 ◇ q31) = (q32 ◇ q34):=by
    intro q31 q32 q33 q34
    exact ((apc23 q31 q33 q34).symm).trans (apc22 q32 q33 q34)
  exact (apc24 y (x ◇ y) x ((z ◇ z) ◇ w)).trans ((apc24 w (x ◇ y) (z ◇ z) ((z ◇ z) ◇ w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47394_to_405 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47394_to_405
