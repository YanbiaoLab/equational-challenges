-- Equation48905 → Equation54622
-- Recorded verdict: true
-- Premise: x * y = ((y * x) * x) * (z * x)
-- Conclusion: x * (y * z) = w * (w * (x * y))
-- Original submission SHA-256: d35174132b255f786422e924654eecb7a801dff556ef5ceb1076a2965c988bb4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ x) ◇ x) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = w ◇ (w ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ x) ◇ x) ◇ (z ◇ x)) = (((y ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), (((y ◇ x) ◇ x) ◇ (x ◇ x)) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (((q3 ◇ (q2 ◇ q0)) ◇ (q2 ◇ q0)) ◇ (q0 ◇ q1)) = ((q2 ◇ q0) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q3 ◇ (q2 ◇ q0)) ◇ (q2 ◇ q0)) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q0) q3 ((q1 ◇ q0) ◇ q0)).symm)
  have apc3 : forall (q4 q5 q6:G), (((q6 ◇ q6) ◇ q4) ◇ (q6 ◇ q5)) = ((q6 ◇ q6) ◇ (q4 ◇ (q6 ◇ q6))):=by
    intro q4 q5 q6
    exact ((cg (fun t => t ◇ (q6 ◇ q5)) (apc2 q6 q6 q6 q4)).symm).trans (apc2 q6 q5 q6 (q4 ◇ (q6 ◇ q6)))
  have apc4 : forall (q7:G), ((q7 ◇ q7) ◇ (q7 ◇ (q7 ◇ q7))) = (q7 ◇ q7):=by
    intro q7
    exact ((apc3 q7 q7 q7).symm).trans ((h q7 q7 q7).symm)
  have apc5 : forall (q4 q5 q6:G), (((q6 ◇ q6) ◇ q4) ◇ (q6 ◇ q5)) = (((q6 ◇ q6) ◇ q4) ◇ (q6 ◇ q4)):=by
    intro q4 q5 q6
    exact (apc3 q4 q5 q6).trans ((apc3 q4 q4 q6).symm)
  have apc6 : forall (q8 q9:G), ((q9 ◇ q9) ◇ ((q9 ◇ q9) ◇ q8)) = ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ q9)):=by
    intro q8 q9
    exact ((cg (fun t => t ◇ ((q9 ◇ q9) ◇ q8)) (apc4 q9)).symm).trans (((cg (fun t => t ◇ ((q9 ◇ q9) ◇ q8)) (cg (fun t => t ◇ (q9 ◇ (q9 ◇ q9))) (apc4 q9))).symm).trans (apc2 (q9 ◇ q9) q8 q9 (q9 ◇ q9)))
  have apc8 : forall (q10:G), ((q10 ◇ (q10 ◇ q10)) ◇ (q10 ◇ q10)) = ((q10 ◇ q10) ◇ (q10 ◇ q10)):=by
    intro q10
    exact (((cg (fun t => (q10 ◇ q10) ◇ t) (apc4 q10)).symm).trans (apc6 (q10 ◇ (q10 ◇ q10)) q10)).symm
  have apc9 : forall (q11:G), ((q11 ◇ q11) ◇ (q11 ◇ q11)) = (q11 ◇ q11):=by
    intro q11
    exact ((apc1 (q11 ◇ q11) (q11 ◇ q11) ((((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ (q11 ◇ q11)) ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11)))).symm).trans ((((cg (fun t => t ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (cg (fun t => t ◇ (q11 ◇ q11)) (apc8 q11))).symm).trans (apc1 (q11 ◇ q11) (q11 ◇ (q11 ◇ q11)) q11)).trans (apc4 q11))
  have apc10 : forall (q12 q13:G), ((q13 ◇ q13) ◇ (q13 ◇ q12)) = (q13 ◇ q13):=by
    intro q12 q13
    exact (((cg (fun t => t ◇ (q13 ◇ q12)) (apc9 q13)).symm).trans (apc5 (q13 ◇ q13) q12 q13)).trans ((cg (fun t => t ◇ (q13 ◇ (q13 ◇ q13))) (apc9 q13)).trans (apc4 q13))
  have apc11 : forall (q14 q15 q16:G), ((q16 ◇ q16) ◇ (q14 ◇ q15)) = ((q16 ◇ q14) ◇ (q16 ◇ q16)):=by
    intro q14 q15 q16
    exact ((cg (fun t => t ◇ (q14 ◇ q15)) (apc10 q14 q16)).symm).trans (((cg (fun t => t ◇ (q14 ◇ q15)) (cg (fun t => t ◇ (q16 ◇ q14)) (apc10 q14 q16))).symm).trans (apc2 q14 q15 q16 (q16 ◇ q16)))
  have apc12 : forall (q10 q11:G), ((q10 ◇ (q10 ◇ q10)) ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10 q11
    exact (apc8 q10).trans (apc9 q10)
  have apc13 : forall (q17:G), ((q17 ◇ q17) ◇ q17) = (q17 ◇ q17):=by
    intro q17
    exact ((((cg (fun t => (q17 ◇ q17) ◇ t) (apc10 q17 q17)).trans (apc10 q17 q17)).symm).trans (((cg (fun t => t ◇ ((q17 ◇ q17) ◇ (q17 ◇ q17))) (apc12 q17 q17)).symm).trans (apc1 (q17 ◇ q17) q17 q17))).symm
  have apc14 : forall (q18:G), (q18 ◇ (q18 ◇ q18)) = (q18 ◇ q18):=by
    intro q18
    exact ((((cg (fun t => t ◇ (q18 ◇ q18)) (apc13 q18)).trans (apc10 q18 q18)).symm).trans (((cg (fun t => t ◇ (q18 ◇ q18)) (cg (fun t => t ◇ q18) (apc13 q18))).symm).trans (apc1 q18 (q18 ◇ q18) q18))).symm
  have apc15 : forall (q19 q20:G), ((q19 ◇ q20) ◇ (q19 ◇ q19)) = (q19 ◇ q19):=by
    intro q19 q20
    exact (((cg (fun t => t ◇ (q20 ◇ (q19 ◇ q19))) (apc10 q19 q19)).trans (apc11 q20 (q19 ◇ q19) q19)).symm).trans ((((cg (fun t => t ◇ (q20 ◇ (q19 ◇ q19))) (cg (fun t => t ◇ (q19 ◇ q19)) (apc12 q19 q19))).symm).trans ((h (q19 ◇ q19) (q19 ◇ (q19 ◇ q19)) q20).symm)).trans ((cg (fun t => (q19 ◇ q19) ◇ t) (apc14 q19)).trans (apc10 q19 q19)))
  have apc17 : forall (q21 q22:G), ((q21 ◇ q21) ◇ (q22 ◇ q21)) = (q21 ◇ q21):=by
    intro q21 q22
    exact ((cg (fun t => t ◇ (q22 ◇ q21)) (apc13 q21)).symm).trans ((h q21 q21 q22).symm)
  have apc18 : forall (q14 q15 q16 q19 q20:G), ((q16 ◇ q16) ◇ (q14 ◇ q15)) = (q16 ◇ q16):=by
    intro q14 q15 q16 q19 q20
    exact (apc11 q14 q15 q16).trans (apc15 q16 q14)
  have apc19 : forall (q23 q24:G), ((q24 ◇ q23) ◇ (q23 ◇ q23)) = (q23 ◇ q23):=by
    intro q23 q24
    exact ((((cg (fun t => t ◇ (q23 ◇ q23)) (apc18 q24 q23 q23 ((q23 ◇ q23) ◇ (q24 ◇ q23)) ((q23 ◇ q23) ◇ (q24 ◇ q23)))).trans (apc18 q23 q23 q23 ((q23 ◇ q23) ◇ (q23 ◇ q23)) ((q23 ◇ q23) ◇ (q23 ◇ q23)))).symm).trans (((cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ (q24 ◇ q23)) (apc17 q23 q24))).symm).trans (apc2 q23 q23 q24 (q23 ◇ q23)))).symm
  have apc20 : forall (x y z q23 q24:G), (x ◇ y) = (x ◇ x):=by
    intro x y z q23 q24
    exact (((apc19 x (y ◇ x)).symm).trans (apc1 x y x)).symm
  have apc21 : forall (q25 q26 q27:G), (((q26 ◇ q26) ◇ (q25 ◇ q25)) ◇ (q27 ◇ q27)) = (q25 ◇ q25):=by
    intro q25 q26 q27
    exact ((((cg (fun t => t ◇ (q27 ◇ (q25 ◇ q25))) (cg (fun t => (q26 ◇ q26) ◇ t) (apc20 q25 q25 (q25 ◇ q25) (q25 ◇ q25) (q25 ◇ q25)))).trans (cg (fun t => ((q26 ◇ q26) ◇ (q25 ◇ q25)) ◇ t) (cg (fun t => q27 ◇ t) (apc20 q25 q25 (q25 ◇ q25) (q25 ◇ q25) (q25 ◇ q25))))).trans (cg (fun t => ((q26 ◇ q26) ◇ (q25 ◇ q25)) ◇ t) (apc20 q27 (q25 ◇ q25) (q27 ◇ (q25 ◇ q25)) (q27 ◇ (q25 ◇ q25)) (q27 ◇ (q25 ◇ q25))))).symm).trans ((((cg (fun t => t ◇ (q27 ◇ (q25 ◇ q25))) (cg (fun t => t ◇ (q25 ◇ q25)) (apc18 q25 q25 q26 q25 q25))).symm).trans ((h (q25 ◇ q25) (q26 ◇ q26) q27).symm)).trans (((cg (fun t => t ◇ (q26 ◇ q26)) (apc20 q25 q25 (q25 ◇ q25) (q25 ◇ q25) (q25 ◇ q25))).trans (apc20 (q25 ◇ q25) (q26 ◇ q26) ((q25 ◇ q25) ◇ (q26 ◇ q26)) ((q25 ◇ q25) ◇ (q26 ◇ q26)) ((q25 ◇ q25) ◇ (q26 ◇ q26)))).trans (apc19 q25 q25)))
  have apc22 : forall (q28 q29:G), (q29 ◇ q29) = (q28 ◇ q28):=by
    intro q28 q29
    exact (((((((cg (fun t => ((q28 ◇ q28) ◇ (q29 ◇ q29)) ◇ t) (apc20 q28 (q29 ◇ q29) (q28 ◇ (q29 ◇ q29)) (q28 ◇ (q29 ◇ q29)) (q28 ◇ (q29 ◇ q29)))).trans (cg (fun t => t ◇ (q28 ◇ q28)) (apc20 (q28 ◇ q28) (q29 ◇ q29) ((q28 ◇ q28) ◇ (q29 ◇ q29)) ((q28 ◇ q28) ◇ (q29 ◇ q29)) ((q28 ◇ q28) ◇ (q29 ◇ q29))))).trans (cg (fun t => t ◇ (q28 ◇ q28)) (apc19 q28 q28))).trans (apc20 (q28 ◇ q28) (q28 ◇ q28) ((q28 ◇ q28) ◇ (q28 ◇ q28)) ((q28 ◇ q28) ◇ (q28 ◇ q28)) ((q28 ◇ q28) ◇ (q28 ◇ q28)))).trans (apc19 q28 q28)).symm).trans ((((cg (fun t => t ◇ (q28 ◇ (q29 ◇ q29))) (cg (fun t => t ◇ (q29 ◇ q29)) (apc21 q28 q28 q29))).symm).trans ((h (q29 ◇ q29) ((q28 ◇ q28) ◇ (q28 ◇ q28)) q28).symm)).trans ((apc20 (q29 ◇ q29) ((q28 ◇ q28) ◇ (q28 ◇ q28)) ((q29 ◇ q29) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))) ((q29 ◇ q29) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))) ((q29 ◇ q29) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28)))).trans (apc19 q29 q29)))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc20 x (y ◇ z) w w w
    _ = (w ◇ w):=(apc22 x w).symm
    _ = (w ◇ (w ◇ (x ◇ y))):=(apc20 w (w ◇ (x ◇ y)) w w w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48905_to_54622 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48905_to_54622
