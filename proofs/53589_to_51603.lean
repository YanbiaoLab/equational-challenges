-- Equation53589 → Equation51603
-- Recorded verdict: true
-- Premise: x * y = (((z * z) * x) * x) * x
-- Conclusion: x * y = ((y * y) * (z * w)) * u
-- Original submission SHA-256: 699797ea3ababb6aee5743591c034014a389a35a82be06ce69169c44a86f6683
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((z ◇ z) ◇ x) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((y ◇ y) ◇ (z ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc3 : forall (q0 q1 q2:G), ((((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q0) (apc0 ((q1 ◇ q1) ◇ q0) q0 q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc4 : forall (q3 q4:G), (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3) = (q3 ◇ q3):=by
    intro q3 q4
    exact ((cg (fun t => t ◇ q3) (cg (fun t => (q3 ◇ q3) ◇ t) (apc3 q3 q4 ((((q4 ◇ q4) ◇ q3) ◇ ((q4 ◇ q4) ◇ q3)) ◇ q3)))).symm).trans (((cg (fun t => t ◇ q3) (cg (fun t => t ◇ ((((q4 ◇ q4) ◇ q3) ◇ ((q4 ◇ q4) ◇ q3)) ◇ q3)) (apc3 q3 q4 q4))).symm).trans (apc3 q3 ((q4 ◇ q4) ◇ q3) q4))
  have apc5 : forall (q5 q6:G), (((q5 ◇ q5) ◇ q5) ◇ q5) = (q5 ◇ q5):=by
    intro q5 q6
    exact (((cg (fun t => t ◇ q5) (cg (fun t => t ◇ q5) (apc3 q5 q5 q5))).symm).trans ((h q5 q6 ((q5 ◇ q5) ◇ q5)).symm)).trans (apc0 q5 q6 (q5 ◇ q6))
  have apc6 : forall (q7 q8:G), ((q7 ◇ q7) ◇ q7) = (q7 ◇ q7):=by
    intro q7 q8
    exact (((cg (fun t => t ◇ q7) (apc5 q7 q7)).symm).trans ((h q7 q8 q7).symm)).trans (apc0 q7 q8 (q7 ◇ q8))
  have apc7 : forall (q9:G), (((q9 ◇ q9) ◇ (q9 ◇ q9)) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) = (q9 ◇ q9):=by
    intro q9
    exact (((apc4 q9 q9).symm).trans (apc0 ((q9 ◇ q9) ◇ (q9 ◇ q9)) q9 q9)).symm
  have apc8 : forall (q10 q11 q12:G), (((q11 ◇ q11) ◇ q10) ◇ (q11 ◇ q11)) = ((q11 ◇ q11) ◇ q12):=by
    intro q10 q11 q12
    exact ((cg (fun t => t ◇ (q11 ◇ q11)) ((h (q11 ◇ q11) q10 q11).symm)).symm).trans ((h (q11 ◇ q11) q12 (q11 ◇ q11)).symm)
  have apc9 : forall (q13 q14:G), (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ q14) = (q13 ◇ q13):=by
    intro q13 q14
    exact ((((cg (fun t => t ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) (apc0 (q13 ◇ q13) ((q13 ◇ q13) ◇ (q13 ◇ q13)) ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))))).trans (apc7 q13)).symm).trans (((cg (fun t => t ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) (cg (fun t => t ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) (apc7 q13))).symm).trans ((h ((q13 ◇ q13) ◇ (q13 ◇ q13)) q14 (q13 ◇ q13)).symm))).symm
  have apc10 : forall (q15 q16 q17:G), (((q15 ◇ q15) ◇ q16) ◇ q16) = (q16 ◇ q16):=by
    intro q15 q16 q17
    exact (((cg (fun t => t ◇ q16) (cg (fun t => t ◇ q16) (apc9 q15 q16))).symm).trans ((h q16 q17 (q15 ◇ q15)).symm)).trans (apc0 q16 q17 (q16 ◇ q17))
  have apc13 : forall (q18 q19 q20:G), ((((q19 ◇ q19) ◇ q18) ◇ (q19 ◇ q19)) ◇ q20) = (q19 ◇ q19):=by
    intro q18 q19 q20
    exact ((cg (fun t => t ◇ q20) ((apc8 q18 q19 (q19 ◇ q19)).symm)).symm).trans (apc9 q19 q20)
  have apc14 : forall (q10 q12 q11 q21:G), ((q12 ◇ q12) ◇ (q12 ◇ q12)) = (q12 ◇ q10):=by
    intro q10 q12 q11 q21
    exact (((h q12 q10 q11).trans (h (((q11 ◇ q11) ◇ q12) ◇ q12) q12 q21)).trans (((((cg (fun t => t ◇ (((q11 ◇ q11) ◇ q12) ◇ q12)) (cg (fun t => t ◇ (((q11 ◇ q11) ◇ q12) ◇ q12)) (cg (fun t => (q21 ◇ q21) ◇ t) (apc10 q11 q12 (((q11 ◇ q11) ◇ q12) ◇ q12))))).trans (cg (fun t => t ◇ (((q11 ◇ q11) ◇ q12) ◇ q12)) (cg (fun t => ((q21 ◇ q21) ◇ (q12 ◇ q12)) ◇ t) (apc10 q11 q12 (((q11 ◇ q11) ◇ q12) ◇ q12))))).trans (cg (fun t => (((q21 ◇ q21) ◇ (q12 ◇ q12)) ◇ (q12 ◇ q12)) ◇ t) (apc10 q11 q12 (((q11 ◇ q11) ◇ q12) ◇ q12)))).trans (cg (fun t => t ◇ (q12 ◇ q12)) (apc10 q21 (q12 ◇ q12) (((q21 ◇ q21) ◇ (q12 ◇ q12)) ◇ (q12 ◇ q12))))).trans (apc6 (q12 ◇ q12) (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ (q12 ◇ q12))))).symm
  have apc15 : forall (q22 q23 q24:G), (((q23 ◇ q22) ◇ (q23 ◇ q22)) ◇ q24) = (q23 ◇ q23):=by
    intro q22 q23 q24
    exact ((cg (fun t => t ◇ q24) (apc0 (q23 ◇ q22) (q23 ◇ q23) ((q23 ◇ q22) ◇ (q23 ◇ q23)))).symm).trans (((cg (fun t => t ◇ q24) (cg (fun t => t ◇ (q23 ◇ q23)) (apc14 q22 q23 q22 q22))).symm).trans (apc13 (q23 ◇ q23) q23 q24))
  have apc20 : forall (q11 q25 q21 q12:G), (q25 ◇ q25) = (q11 ◇ q11):=by
    intro q11 q25 q21 q12
    exact ((((((cg (fun t => t ◇ q25) (cg (fun t => t ◇ ((q21 ◇ q21) ◇ q25)) (cg (fun t => t ◇ ((q21 ◇ q21) ◇ q25)) (apc0 (q11 ◇ q11) ((q21 ◇ q21) ◇ q25) ((q11 ◇ q11) ◇ ((q21 ◇ q21) ◇ q25)))))).trans (cg (fun t => t ◇ q25) (cg (fun t => t ◇ ((q21 ◇ q21) ◇ q25)) (apc15 q11 q11 ((q21 ◇ q21) ◇ q25))))).trans (cg (fun t => t ◇ q25) (apc0 (q11 ◇ q11) ((q21 ◇ q21) ◇ q25) ((q11 ◇ q11) ◇ ((q21 ◇ q21) ◇ q25))))).trans (apc15 q11 q11 q25)).symm).trans ((((cg (fun t => t ◇ q25) (h ((q21 ◇ q21) ◇ q25) q25 q11)).symm).trans ((h q25 q12 q21).symm)).trans (apc0 q25 q12 (q25 ◇ q12)))).symm
  have apc32 : forall (q26 q27 q28:G), (q28 ◇ q27) = (q26 ◇ q26):=by
    intro q26 q27 q28
    exact (((apc20 q26 (q28 ◇ q28) q26 q26).symm).trans (apc14 q27 q28 q26 q26)).symm
  exact (apc32 (x ◇ y) y x).trans ((apc32 (x ◇ y) u ((y ◇ y) ◇ (z ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53589_to_51603 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53589_to_51603
