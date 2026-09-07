-- Equation51734 → Equation48415
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (w * x)) * z
-- Conclusion: x * y = (z * (w * x)) * (z * y)
-- Original submission SHA-256: 1bfde77431b41188bb3cc91c4f2897c308de2c061ed900cb75e749429d9fa351
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ (w ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ x)) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc1 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (((q5 ◇ q4) ◇ q3) ◇ q5) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((cg (fun t => t ◇ q5) (apc0 q3 (q5 ◇ q4) (q3 ◇ q4))).symm).trans ((h q4 q6 q5 q3).symm)).trans (apc1 q4 q6 (q4 ◇ q6) (q4 ◇ q6))
  have apc3 : forall (q7 q8 q9 q10 q11:G), (q8 ◇ q8) = (q7 ◇ q7):=by
    intro q7 q8 q9 q10 q11
    exact ((((apc2 q9 q7 q10 q9).symm).trans (h ((q10 ◇ q7) ◇ q9) q10 q8 q11)).trans (((cg (fun t => t ◇ q8) (cg (fun t => (q8 ◇ ((q10 ◇ q7) ◇ q9)) ◇ t) (apc1 q11 ((q10 ◇ q7) ◇ q9) (q11 ◇ ((q10 ◇ q7) ◇ q9)) (q11 ◇ ((q10 ◇ q7) ◇ q9))))).trans (cg (fun t => t ◇ q8) (cg (fun t => t ◇ (q11 ◇ q11)) (apc1 q8 ((q10 ◇ q7) ◇ q9) (q8 ◇ ((q10 ◇ q7) ◇ q9)) (q8 ◇ ((q10 ◇ q7) ◇ q9)))))).trans (apc2 (q11 ◇ q11) q8 q8 (((q8 ◇ q8) ◇ (q11 ◇ q11)) ◇ q8)))).symm
  have apc4 : forall (q12 q13 q14 q15:G), ((q12 ◇ q12) ◇ q14) = (q13 ◇ q13):=by
    intro q12 q13 q14 q15
    exact ((((cg (fun t => t ◇ q14) (cg (fun t => t ◇ q12) (cg (fun t => (q12 ◇ (q14 ◇ q13)) ◇ t) (apc1 q15 (q14 ◇ q13) (q15 ◇ (q14 ◇ q13)) (q15 ◇ (q14 ◇ q13)))))).trans (cg (fun t => t ◇ q14) (cg (fun t => t ◇ q12) (cg (fun t => t ◇ (q15 ◇ q15)) (apc1 q12 (q14 ◇ q13) (q12 ◇ (q14 ◇ q13)) (q12 ◇ (q14 ◇ q13))))))).trans (cg (fun t => t ◇ q14) (apc2 (q15 ◇ q15) q12 q12 (((q12 ◇ q12) ◇ (q15 ◇ q15)) ◇ q12)))).symm).trans (((cg (fun t => t ◇ q14) (h (q14 ◇ q13) q15 q12 q15)).symm).trans (apc2 q15 q13 q14 q15))
  have apc6 : forall (q16 q17 q18:G), ((q16 ◇ q16) ◇ q17) = (q17 ◇ q17):=by
    intro q16 q17 q18
    exact (((cg (fun t => t ◇ q17) (apc4 q17 q16 (q16 ◇ q17) q16)).symm).trans ((h q17 q18 q17 q16).symm)).trans (apc1 q17 q18 (q17 ◇ q18) (q17 ◇ q18))
  have apc8 : forall (q19 q20 q21:G), (((q21 ◇ q20) ◇ q19) ◇ ((q21 ◇ q20) ◇ q19)) = (q20 ◇ q20):=by
    intro q19 q20 q21
    exact (((apc2 q19 q20 q21 q19).symm).trans (apc1 ((q21 ◇ q20) ◇ q19) q21 q19 q19)).symm
  have apc9 : forall (q22 q23 q24 q25 q26:G), (((q24 ◇ q23) ◇ q22) ◇ q25) = (q23 ◇ q23):=by
    intro q22 q23 q24 q25 q26
    exact ((((((cg (fun t => t ◇ ((q24 ◇ q23) ◇ q22)) (cg (fun t => (q23 ◇ q23) ◇ t) (apc1 q26 ((q24 ◇ q23) ◇ q22) (q26 ◇ ((q24 ◇ q23) ◇ q22)) (q26 ◇ ((q24 ◇ q23) ◇ q22))))).trans (cg (fun t => t ◇ ((q24 ◇ q23) ◇ q22)) (apc1 (q23 ◇ q23) (q26 ◇ q26) ((q23 ◇ q23) ◇ (q26 ◇ q26)) ((q23 ◇ q23) ◇ (q26 ◇ q26))))).trans (apc6 (q23 ◇ q23) ((q24 ◇ q23) ◇ q22) (((q23 ◇ q23) ◇ (q23 ◇ q23)) ◇ ((q24 ◇ q23) ◇ q22)))).trans (apc8 q22 q23 q24)).symm).trans (((cg (fun t => t ◇ ((q24 ◇ q23) ◇ q22)) (cg (fun t => t ◇ (q26 ◇ ((q24 ◇ q23) ◇ q22))) (apc8 q22 q23 q24))).symm).trans ((h ((q24 ◇ q23) ◇ q22) q25 ((q24 ◇ q23) ◇ q22) q26).symm))).symm
  have apc10 : forall (q19 q20 q21:G), ((q20 ◇ q20) ◇ (q20 ◇ q20)) = (q20 ◇ q20):=by
    intro q19 q20 q21
    exact (((apc9 q19 q20 q21 ((q21 ◇ q20) ◇ q19) (((q21 ◇ q20) ◇ q19) ◇ ((q21 ◇ q20) ◇ q19))).symm).trans (((apc8 q19 q20 q21).trans ((apc8 q20 q20 q20).symm)).trans ((cg (fun t => t ◇ ((q20 ◇ q20) ◇ q20)) (apc6 q20 q20 ((q20 ◇ q20) ◇ q20))).trans (cg (fun t => (q20 ◇ q20) ◇ t) (apc6 q20 q20 ((q20 ◇ q20) ◇ q20)))))).symm
  have apc11 : forall (q27 q28:G), ((q28 ◇ q27) ◇ (q28 ◇ q27)) = (q27 ◇ q27):=by
    intro q27 q28
    exact ((apc10 q27 (q28 ◇ q27) q27).symm).trans (apc9 (q28 ◇ q27) q27 q28 ((q28 ◇ q27) ◇ (q28 ◇ q27)) q27)
  have apc12 : forall (q29 q30 q31 q32:G), ((q30 ◇ q29) ◇ q31) = (q29 ◇ q29):=by
    intro q29 q30 q31 q32
    exact (((((((cg (fun t => t ◇ (q30 ◇ q29)) (cg (fun t => (q29 ◇ q29) ◇ t) (apc1 q32 (q30 ◇ q29) (q32 ◇ (q30 ◇ q29)) (q32 ◇ (q30 ◇ q29))))).trans (cg (fun t => t ◇ (q30 ◇ q29)) (apc1 (q29 ◇ q29) (q32 ◇ q32) ((q29 ◇ q29) ◇ (q32 ◇ q32)) ((q29 ◇ q29) ◇ (q32 ◇ q32))))).trans (cg (fun t => t ◇ (q30 ◇ q29)) (apc11 q29 q29))).trans (apc1 (q29 ◇ q29) (q30 ◇ q29) ((q29 ◇ q29) ◇ (q30 ◇ q29)) ((q29 ◇ q29) ◇ (q30 ◇ q29)))).trans (apc11 q29 q29)).symm).trans (((cg (fun t => t ◇ (q30 ◇ q29)) (cg (fun t => t ◇ (q32 ◇ (q30 ◇ q29))) (apc11 q29 q30))).symm).trans ((h (q30 ◇ q29) q31 (q30 ◇ q29) q32).symm))).symm
  exact (calc
    (x ◇ y) = (x ◇ x):=apc1 x y w w
    _ = ((w ◇ x) ◇ (w ◇ x)):=(apc3 x (w ◇ x) w w w).symm
    _ = ((z ◇ (w ◇ x)) ◇ (z ◇ y)):=(apc12 (w ◇ x) z (z ◇ y) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51734_to_48415 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51734_to_48415
