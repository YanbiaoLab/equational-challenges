-- Equation34883 → Equation36095
-- Recorded verdict: true
-- Premise: x = ((y * y) * ((x * y) * z)) * x
-- Conclusion: x = ((y * (z * z)) * (z * w)) * x
-- Original submission SHA-256: 1dcb482b374b1760ff6a2ec6c2b6101c3c845f2552e7b3c3dea1a68e80b469b7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ ((x ◇ y) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ z)) ◇ (z ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ y) ◇ ((x ◇ y) ◇ z)) ◇ x) = (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2 q3:G), (((((q3 ◇ q1) ◇ q2) ◇ ((q3 ◇ q1) ◇ q2)) ◇ q3) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q1 q2 q3
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => (((q3 ◇ q1) ◇ q2) ◇ ((q3 ◇ q1) ◇ q2)) ◇ t) ((h q3 q1 q2).symm))).symm).trans ((h (q1 ◇ q1) ((q3 ◇ q1) ◇ q2) q3).symm)
  have apc4 : forall (q1 q2 q4 q3:G), (((q4 ◇ q4) ◇ (q4 ◇ q3)) ◇ ((q1 ◇ q1) ◇ ((q4 ◇ q1) ◇ q2))) = ((q1 ◇ q1) ◇ ((q4 ◇ q1) ◇ q2)):=by
    intro q1 q2 q4 q3
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q4 ◇ q1) ◇ q2))) (cg (fun t => (q4 ◇ q4) ◇ t) (cg (fun t => t ◇ q3) ((h q4 q1 q2).symm)))).symm).trans ((h ((q1 ◇ q1) ◇ ((q4 ◇ q1) ◇ q2)) q4 q3).symm)
  have apc8 : forall (q5 q6 q7 q8:G), ((((q7 ◇ q8) ◇ (q7 ◇ q8)) ◇ ((q5 ◇ q5) ◇ ((q7 ◇ q5) ◇ q6))) ◇ (q7 ◇ q7)) = (q7 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((cg (fun t => t ◇ (q7 ◇ q7)) (cg (fun t => ((q7 ◇ q8) ◇ (q7 ◇ q8)) ◇ t) (apc4 q5 q6 q7 q8))).symm).trans ((h (q7 ◇ q7) (q7 ◇ q8) ((q5 ◇ q5) ◇ ((q7 ◇ q5) ◇ q6))).symm)
  have apc9 : forall (q9 q10 q11:G), (((q9 ◇ q9) ◇ ((q11 ◇ q9) ◇ q10)) ◇ (q11 ◇ q11)) = (q11 ◇ q11):=by
    intro q9 q10 q11
    exact ((cg (fun t => t ◇ (q11 ◇ q11)) (apc4 q9 q10 q11 q11)).symm).trans (apc8 q9 q10 q11 q11)
  have apc10 : forall (q12 q13 q14:G), (((((q14 ◇ q12) ◇ q13) ◇ ((q14 ◇ q12) ◇ q13)) ◇ (q14 ◇ q14)) ◇ (q12 ◇ q12)) = (q12 ◇ q12):=by
    intro q12 q13 q14
    exact ((cg (fun t => t ◇ (q12 ◇ q12)) (cg (fun t => (((q14 ◇ q12) ◇ q13) ◇ ((q14 ◇ q12) ◇ q13)) ◇ t) (apc9 q12 q13 q14))).symm).trans ((h (q12 ◇ q12) ((q14 ◇ q12) ◇ q13) (q14 ◇ q14)).symm)
  have apc13 : forall (q15 q16 q17:G), (((q17 ◇ q17) ◇ (q15 ◇ q15)) ◇ (((q17 ◇ q15) ◇ q16) ◇ ((q17 ◇ q15) ◇ q16))) = (((q17 ◇ q15) ◇ q16) ◇ ((q17 ◇ q15) ◇ q16)):=by
    intro q15 q16 q17
    exact ((cg (fun t => t ◇ (((q17 ◇ q15) ◇ q16) ◇ ((q17 ◇ q15) ◇ q16))) (cg (fun t => (q17 ◇ q17) ◇ t) (apc2 q15 q16 q17))).symm).trans ((h (((q17 ◇ q15) ◇ q16) ◇ ((q17 ◇ q15) ◇ q16)) q17 (q15 ◇ q15)).symm)
  have apc14 : forall (q18:G), ((((q18 ◇ q18) ◇ q18) ◇ ((q18 ◇ q18) ◇ q18)) ◇ (q18 ◇ q18)) = (q18 ◇ q18):=by
    intro q18
    exact (((cg (fun t => (((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ (((q18 ◇ q18) ◇ q18) ◇ ((q18 ◇ q18) ◇ q18))) ◇ t) (cg (fun t => q18 ◇ t) (apc1 q18))).trans (cg (fun t => t ◇ (q18 ◇ q18)) (apc13 q18 q18 q18))).symm).trans ((((cg (fun t => (((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ (((q18 ◇ q18) ◇ q18) ◇ ((q18 ◇ q18) ◇ q18))) ◇ t) (cg (fun t => t ◇ (((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ q18)) ◇ q18)) (apc1 q18))).symm).trans (apc13 ((q18 ◇ q18) ◇ q18) q18 (q18 ◇ q18))).trans ((cg (fun t => t ◇ (((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ q18)) ◇ q18)) (apc1 q18)).trans (cg (fun t => q18 ◇ t) (apc1 q18))))
  have apc15 : forall (q19:G), ((q19 ◇ q19) ◇ (q19 ◇ q19)) = (q19 ◇ q19):=by
    intro q19
    exact ((cg (fun t => t ◇ (q19 ◇ q19)) (apc14 q19)).symm).trans (apc10 q19 q19 q19)
  have apc16 : forall (q20:G), ((q20 ◇ q20) ◇ q20) = q20:=by
    intro q20
    exact ((cg (fun t => t ◇ q20) (apc15 q20)).symm).trans (((cg (fun t => t ◇ q20) (cg (fun t => (q20 ◇ q20) ◇ t) (apc15 q20))).symm).trans ((h q20 q20 (q20 ◇ q20)).symm))
  have apc18 : forall (q20 q0:G), (q0 ◇ q0) = q0:=by
    intro q20 q0
    exact (((cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ q0) ◇ t) (apc16 q0))).trans (cg (fun t => t ◇ q0) (apc16 q0))).symm).trans (apc1 q0)
  have apc19 : forall (q21 q22:G), ((q22 ◇ (q21 ◇ q22)) ◇ q21) = q21:=by
    intro q21 q22
    exact ((cg (fun t => t ◇ q21) (cg (fun t => t ◇ (q21 ◇ q22)) (apc18 (q22 ◇ q22) q22))).symm).trans (((cg (fun t => t ◇ q21) (cg (fun t => (q22 ◇ q22) ◇ t) (apc18 q21 (q21 ◇ q22)))).symm).trans ((h q21 q22 (q21 ◇ q22)).symm))
  have apc23 : forall (q23 q24 q25:G), ((((q25 ◇ q23) ◇ q24) ◇ q25) ◇ q23) = q23:=by
    intro q23 q24 q25
    exact ((((((((cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => (q25 ◇ q25) ◇ t) (cg (fun t => t ◇ q25) (apc18 (q25 ◇ q25) q25)))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => t ◇ (q25 ◇ q25)) (apc18 (q25 ◇ q25) q25)))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => q25 ◇ t) (apc18 (q25 ◇ q25) q25)))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ◇ t) (cg (fun t => t ◇ q25) (apc18 (q25 ◇ q25) q25))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ◇ t) (apc18 (q25 ◇ q25) q25)))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ q25) (apc18 (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ((q25 ◇ q23) ◇ q24))))).trans (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ q25) ◇ t) (apc18 (q23 ◇ q23) q23))).symm).trans ((((cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (((q25 ◇ q23) ◇ q24) ◇ ((q25 ◇ q23) ◇ q24)) ◇ t) (apc0 q25 q23 q24))).symm).trans (apc0 (q23 ◇ q23) ((q25 ◇ q23) ◇ q24) q25)).trans (((((((((((cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => ((q23 ◇ q23) ◇ (q23 ◇ q23)) ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ (q23 ◇ q23)) (apc18 (q23 ◇ q23) q23))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => ((q23 ◇ q23) ◇ (q23 ◇ q23)) ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => q23 ◇ t) (apc18 (q23 ◇ q23) q23)))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) (cg (fun t => t ◇ (q23 ◇ q23)) (apc18 (q23 ◇ q23) q23))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) (cg (fun t => q23 ◇ t) (apc18 (q23 ◇ q23) q23))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (q23 ◇ q23) ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (apc18 (q23 ◇ q23) q23))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => (q23 ◇ q23) ◇ t) (cg (fun t => q23 ◇ t) (apc18 (q23 ◇ q23) q23))))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ (q23 ◇ q23)) (apc18 (q23 ◇ q23) q23)))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => q23 ◇ t) (apc18 (q23 ◇ q23) q23)))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (apc18 (q23 ◇ q23) q23))).trans (cg (fun t => q23 ◇ t) (apc18 (q23 ◇ q23) q23))).trans (apc18 (q23 ◇ q23) q23)))
  have apc25 : forall (q26 q27:G), (q27 ◇ q26) = q26:=by
    intro q26 q27
    exact ((cg (fun t => t ◇ q26) (apc19 q27 (q27 ◇ q26))).symm).trans (apc23 q26 (q27 ◇ (q27 ◇ q26)) q27)
  exact (apc25 x ((y ◇ (z ◇ z)) ◇ (z ◇ w))).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34883_to_36095 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34883_to_36095
