-- Equation33119 → Equation280
-- Recorded verdict: true
-- Premise: x = (y ◇ (((y ◇ x) ◇ x) ◇ z)) ◇ x
-- Conclusion: x = ((y ◇ y) ◇ x) ◇ x
-- Original submission SHA-256: 2c5fa42a812c8c5784f81c2ecf83c11bee897599ec299a86eee29a22954ce35e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (((y ◇ x) ◇ x) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ y) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (((y ◇ x) ◇ x) ◇ z)) ◇ x) = ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), ((q0 ◇ (((q0 ◇ q0) ◇ q0) ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2:G), (((q1 ◇ (((q1 ◇ q1) ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ q2)) ◇ q1) = q1:=by
    intro q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ (((q1 ◇ q1) ◇ q1) ◇ q1)) ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q1) (apc1 q1))))).symm).trans ((h q1 (q1 ◇ (((q1 ◇ q1) ◇ q1) ◇ q1)) q2).symm)
  have apc3 : forall (q3 q4 q5 q6:G), (((q3 ◇ (((q3 ◇ q5) ◇ q5) ◇ q4)) ◇ ((q5 ◇ q5) ◇ q6)) ◇ q5) = q5:=by
    intro q3 q4 q5 q6
    exact ((cg (fun t => t ◇ q5) (cg (fun t => (q3 ◇ (((q3 ◇ q5) ◇ q5) ◇ q4)) ◇ t) (cg (fun t => t ◇ q6) (cg (fun t => t ◇ q5) ((h q5 q3 q4).symm))))).symm).trans ((h q5 (q3 ◇ (((q3 ◇ q5) ◇ q5) ◇ q4)) q6).symm)
  have apc4 : forall (q7 q8 q9:G), ((((q8 ◇ (((q8 ◇ q8) ◇ q8) ◇ q8)) ◇ ((q8 ◇ q8) ◇ q7)) ◇ ((q8 ◇ q8) ◇ q9)) ◇ q8) = q8:=by
    intro q7 q8 q9
    exact ((cg (fun t => t ◇ q8) (cg (fun t => ((q8 ◇ (((q8 ◇ q8) ◇ q8) ◇ q8)) ◇ ((q8 ◇ q8) ◇ q7)) ◇ t) (cg (fun t => t ◇ q9) (cg (fun t => t ◇ q8) (apc2 q8 q7))))).symm).trans ((h q8 ((q8 ◇ (((q8 ◇ q8) ◇ q8) ◇ q8)) ◇ ((q8 ◇ q8) ◇ q7)) q9).symm)
  have apc5 : forall (q10 q11:G), (q11 ◇ ((q11 ◇ q11) ◇ q10)) = ((q11 ◇ q11) ◇ q10):=by
    intro q10 q11
    exact ((cg (fun t => t ◇ ((q11 ◇ q11) ◇ q10)) (apc1 q11)).symm).trans (((cg (fun t => t ◇ ((q11 ◇ q11) ◇ q10)) (cg (fun t => (q11 ◇ (((q11 ◇ q11) ◇ q11) ◇ q11)) ◇ t) (apc4 q10 q11 q10))).symm).trans ((h ((q11 ◇ q11) ◇ q10) (q11 ◇ (((q11 ◇ q11) ◇ q11) ◇ q11)) q11).symm))
  have apc6 : forall (q12 q13:G), (q13 ◇ (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ q12)) = (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ q12):=by
    intro q12 q13
    exact (((cg (fun t => q13 ◇ t) (apc5 q12 (q13 ◇ q13))).symm).trans (apc5 (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ q12) q13)).trans (apc5 q12 (q13 ◇ q13))
  have apc9 : forall (q14 q15:G), (q15 ◇ ((((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) ◇ q14)) = ((((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) ◇ q14):=by
    intro q14 q15
    exact (((cg (fun t => q15 ◇ t) (apc6 q14 (q15 ◇ q15))).symm).trans (apc5 ((((q15 ◇ q15) ◇ (q15 ◇ q15)) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) ◇ q14) q15)).trans (apc6 q14 (q15 ◇ q15))
  have apc10 : forall (q16 q17 q18:G), ((q17 ◇ ((((q17 ◇ q17) ◇ q16) ◇ ((q17 ◇ q17) ◇ q16)) ◇ q18)) ◇ ((q17 ◇ q17) ◇ q16)) = ((q17 ◇ q17) ◇ q16):=by
    intro q16 q17 q18
    exact ((cg (fun t => t ◇ ((q17 ◇ q17) ◇ q16)) (cg (fun t => t ◇ ((((q17 ◇ q17) ◇ q16) ◇ ((q17 ◇ q17) ◇ q16)) ◇ q18)) (apc1 q17))).symm).trans (((cg (fun t => t ◇ ((q17 ◇ q17) ◇ q16)) (cg (fun t => t ◇ ((((q17 ◇ q17) ◇ q16) ◇ ((q17 ◇ q17) ◇ q16)) ◇ q18)) (cg (fun t => (q17 ◇ (((q17 ◇ q17) ◇ q17) ◇ q17)) ◇ t) (apc4 q16 q17 q16)))).symm).trans (apc3 (q17 ◇ (((q17 ◇ q17) ◇ q17) ◇ q17)) q17 ((q17 ◇ q17) ◇ q16) q18))
  have apc11 : forall (q19 q20:G), (((((q19 ◇ q19) ◇ (q19 ◇ q19)) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) ◇ q20) ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) = ((q19 ◇ q19) ◇ (q19 ◇ q19)):=by
    intro q19 q20
    exact ((cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (apc9 q20 q19)).symm).trans (apc10 (q19 ◇ q19) q19 q20)
  have apc12 : forall (q21:G), (((q21 ◇ q21) ◇ (q21 ◇ q21)) ◇ q21) = q21:=by
    intro q21
    exact ((cg (fun t => t ◇ q21) (apc11 q21 ((((((q21 ◇ q21) ◇ (q21 ◇ q21)) ◇ ((q21 ◇ q21) ◇ (q21 ◇ q21))) ◇ q21) ◇ q21) ◇ q21))).symm).trans (apc3 (((q21 ◇ q21) ◇ (q21 ◇ q21)) ◇ ((q21 ◇ q21) ◇ (q21 ◇ q21))) q21 q21 (q21 ◇ q21))
  have apc13 : forall (q22:G), (q22 ◇ q22) = q22:=by
    intro q22
    exact (((cg (fun t => q22 ◇ t) (apc12 q22)).symm).trans (apc6 q22 q22)).trans (apc12 q22)
  have apc14 : forall (q19 q20:G), ((q19 ◇ q20) ◇ q19) = q19:=by
    intro q19 q20
    exact (((((((((((cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ (q19 ◇ q19)) (apc13 q19))))).trans (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => q19 ◇ t) (apc13 q19)))))).trans (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => t ◇ (q19 ◇ q19)) (apc13 q19)))))).trans (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => q19 ◇ t) (apc13 q19)))))).trans (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (cg (fun t => t ◇ (q19 ◇ q19)) (apc13 q19))))).trans (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (cg (fun t => q19 ◇ t) (apc13 q19))))).trans (cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (cg (fun t => t ◇ q20) (apc13 q19)))).trans (cg (fun t => (q19 ◇ q20) ◇ t) (cg (fun t => t ◇ (q19 ◇ q19)) (apc13 q19)))).trans (cg (fun t => (q19 ◇ q20) ◇ t) (cg (fun t => q19 ◇ t) (apc13 q19)))).trans (cg (fun t => (q19 ◇ q20) ◇ t) (apc13 q19))).symm).trans ((apc11 q19 q20).trans (((cg (fun t => t ◇ (q19 ◇ q19)) (apc13 q19)).trans (cg (fun t => q19 ◇ t) (apc13 q19))).trans (apc13 q19)))
  have apc15 : forall (q10 q11:G), (q11 ◇ (q11 ◇ q10)) = (q11 ◇ q10):=by
    intro q10 q11
    exact ((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q10) (apc13 q11))).symm).trans ((apc5 q10 q11).trans (cg (fun t => t ◇ q10) (apc13 q11)))
  have apc17 : forall (q23 q24:G), ((q24 ◇ q23) ◇ q23) = q23:=by
    intro q23 q24
    exact ((cg (fun t => t ◇ q23) (apc15 q23 q24)).symm).trans (((cg (fun t => t ◇ q23) (cg (fun t => q24 ◇ t) (apc14 (q24 ◇ q23) q23))).symm).trans ((h q23 q24 (q24 ◇ q23)).symm))
  exact (apc17 x (y ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_33119_to_280 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_33119_to_280
