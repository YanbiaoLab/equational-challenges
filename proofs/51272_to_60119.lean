-- Equation51272 → Equation60119
-- Recorded verdict: true
-- Premise: x * x = ((y * y) * (x * z)) * y
-- Conclusion: (x * x) * y = (z * z) * (w * y)
-- Original submission SHA-256: 3c04c2f8d5fcd30eae3f8d0d14077487d578a192d45ea4bd7509f840a31cf79c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ y) ◇ (x ◇ z)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (z ◇ z) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ y) ◇ (x ◇ z)) ◇ y) = (((x ◇ x) ◇ (x ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) = (q0 ◇ q0):=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2:G), (((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ ((q1 ◇ q2) ◇ (q1 ◇ q2))) = (q1 ◇ q1):=by
    intro q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q2) ◇ (q1 ◇ q2))) ((h (q1 ◇ q2) (q1 ◇ q2) (q1 ◇ q2)).symm)).symm).trans ((h q1 ((q1 ◇ q2) ◇ (q1 ◇ q2)) q2).symm)
  have apc3 : forall (q3 q4:G), ((q3 ◇ q4) ◇ (q3 ◇ q4)) = ((q3 ◇ q3) ◇ (q3 ◇ q4)):=by
    intro q3 q4
    exact (((cg (fun t => t ◇ (q3 ◇ q4)) (apc2 q3 q4)).symm).trans ((h (q3 ◇ q4) (q3 ◇ q4) (q3 ◇ q4)).symm)).symm
  have apc4 : forall (q5 q6:G), ((q5 ◇ q5) ◇ (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q6)))) = ((q5 ◇ q5) ◇ (q5 ◇ q6)):=by
    intro q5 q6
    exact ((((cg (fun t => (q5 ◇ q5) ◇ t) (cg (fun t => t ◇ ((q5 ◇ q6) ◇ (q5 ◇ q6))) (apc3 q5 q6))).trans (cg (fun t => (q5 ◇ q5) ◇ t) (cg (fun t => ((q5 ◇ q5) ◇ (q5 ◇ q6)) ◇ t) (apc3 q5 q6)))).trans (cg (fun t => (q5 ◇ q5) ◇ t) (apc3 (q5 ◇ q5) (q5 ◇ q6)))).symm).trans ((((cg (fun t => t ◇ (((q5 ◇ q6) ◇ (q5 ◇ q6)) ◇ ((q5 ◇ q6) ◇ (q5 ◇ q6)))) (apc2 q5 q6)).symm).trans (apc2 (q5 ◇ q6) (q5 ◇ q6))).trans (apc3 q5 q6))
  have apc5 : forall (q7 q8 q9 q2:G), (((q2 ◇ q2) ◇ (q7 ◇ q8)) ◇ ((q2 ◇ q2) ◇ (q7 ◇ q8))) = (((q9 ◇ q9) ◇ (q7 ◇ q7)) ◇ q9):=by
    intro q7 q8 q9 q2
    exact (((cg (fun t => t ◇ q9) (cg (fun t => (q9 ◇ q9) ◇ t) ((h q7 q2 q8).symm))).symm).trans ((h ((q2 ◇ q2) ◇ (q7 ◇ q8)) q9 q2).symm)).symm
  have apc8 : forall (q10 q11 q12:G), (((q12 ◇ q12) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q11))) ◇ q12) = ((q10 ◇ q10) ◇ (q10 ◇ q11)):=by
    intro q10 q11 q12
    exact (((cg (fun t => t ◇ q12) (cg (fun t => (q12 ◇ q12) ◇ t) (apc3 q10 q11))).symm).trans ((h (q10 ◇ q11) q12 (q10 ◇ q11)).symm)).trans (apc3 q10 q11)
  have apc9 : forall (q13 q14:G), ((q13 ◇ q13) ◇ (q13 ◇ q14)) = ((q13 ◇ q13) ◇ (q13 ◇ q13)):=by
    intro q13 q14
    exact ((apc8 q13 q14 q13).symm).trans ((h (q13 ◇ q13) q13 (q13 ◇ q14)).symm)
  have apc10 : forall (q3 q4 q13 q14:G), ((q3 ◇ q4) ◇ (q3 ◇ q4)) = ((q3 ◇ q3) ◇ (q3 ◇ q3)):=by
    intro q3 q4 q13 q14
    exact (apc3 q3 q4).trans (apc9 q3 q4)
  have apc11 : forall (q15 q16 q17:G), (((q16 ◇ q16) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) ◇ q16) = ((q15 ◇ q15) ◇ (q15 ◇ q15)):=by
    intro q15 q16 q17
    exact ((cg (fun t => t ◇ q16) (cg (fun t => (q16 ◇ q16) ◇ t) (apc9 q15 q17))).symm).trans (((cg (fun t => t ◇ q16) (cg (fun t => (q16 ◇ q16) ◇ t) (apc4 q15 q17))).symm).trans ((h (q15 ◇ q15) q16 (((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q17)))).symm))
  have apc13 : forall (q10 q11 q18 q19:G), ((((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ (q18 ◇ q19)) ◇ (q10 ◇ q11)) = (q18 ◇ q18):=by
    intro q10 q11 q18 q19
    exact ((cg (fun t => t ◇ (q10 ◇ q11)) (cg (fun t => t ◇ (q18 ◇ q19)) (apc9 q10 q11))).symm).trans (((cg (fun t => t ◇ (q10 ◇ q11)) (cg (fun t => t ◇ (q18 ◇ q19)) (apc3 q10 q11))).symm).trans ((h q18 (q10 ◇ q11) q19).symm))
  have apc15 : forall (q20 q21:G), (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20))) = (q20 ◇ q20):=by
    intro q20 q21
    exact (((cg (fun t => t ◇ ((q20 ◇ q21) ◇ (q20 ◇ q21))) (apc10 q20 q21 ((q20 ◇ q21) ◇ (q20 ◇ q21)) ((q20 ◇ q21) ◇ (q20 ◇ q21)))).trans (cg (fun t => ((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ t) (apc10 q20 q21 ((q20 ◇ q21) ◇ (q20 ◇ q21)) ((q20 ◇ q21) ◇ (q20 ◇ q21))))).symm).trans ((((cg (fun t => t ◇ ((q20 ◇ q21) ◇ (q20 ◇ q21))) ((h (q20 ◇ q21) (q20 ◇ q21) (q20 ◇ q21)).symm)).symm).trans (apc0 q20 ((q20 ◇ q21) ◇ (q20 ◇ q21)) q21)).trans (apc1 q20))
  have apc16 : forall (q22 q23 q24:G), ((q22 ◇ q22) ◇ (q22 ◇ q22)) = (q23 ◇ q23):=by
    intro q22 q23 q24
    exact (((cg (fun t => t ◇ (q22 ◇ q22)) (apc15 q22 q22)).symm).trans ((apc5 (q22 ◇ q22) q24 (q22 ◇ q22) q23).symm)).trans ((apc10 (q23 ◇ q23) ((q22 ◇ q22) ◇ q24) (((q23 ◇ q23) ◇ ((q22 ◇ q22) ◇ q24)) ◇ ((q23 ◇ q23) ◇ ((q22 ◇ q22) ◇ q24))) (((q23 ◇ q23) ◇ ((q22 ◇ q22) ◇ q24)) ◇ ((q23 ◇ q23) ◇ ((q22 ◇ q22) ◇ q24)))).trans (apc15 q23 (((q23 ◇ q23) ◇ (q23 ◇ q23)) ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23)))))
  have apc17 : forall (q25 q26 q27:G), ((q26 ◇ q26) ◇ (q26 ◇ q26)) = ((q25 ◇ q25) ◇ (q26 ◇ q27)):=by
    intro q25 q26 q27
    exact (((cg (fun t => t ◇ (q26 ◇ q27)) (apc16 (q26 ◇ q26) q25 q25)).symm).trans (apc13 q26 q27 (q26 ◇ q26) (q26 ◇ q26))).symm
  have apc18 : forall (q28 q29:G), ((q28 ◇ q28) ◇ (q28 ◇ q28)) = ((q28 ◇ q28) ◇ q29):=by
    intro q28 q29
    exact (((cg (fun t => t ◇ q29) (apc15 q28 (((q28 ◇ q28) ◇ (q28 ◇ q28)) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))))).symm).trans (((cg (fun t => t ◇ q29) ((apc17 q29 (q28 ◇ q28) (q28 ◇ q28)).symm)).symm).trans (apc11 q28 q29 q28))).symm
  have apc23 : forall (q30 q31 q32:G), ((q32 ◇ q32) ◇ (q32 ◇ q32)) = ((q30 ◇ q30) ◇ q31):=by
    intro q30 q31 q32
    exact (((apc18 q30 q31).symm).trans ((apc16 q32 (q30 ◇ q30) q30).symm)).symm
  exact ((apc23 x y ((x ◇ x) ◇ y)).symm).trans (apc23 z (w ◇ y) ((x ◇ x) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51272_to_60119 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51272_to_60119
