-- Equation35768 → Equation28744
-- Recorded verdict: true
-- Premise: x = ((y * (y * x)) * (z * y)) * x
-- Conclusion: x = (((y * y) * x) * y) * (z * x)
-- Original submission SHA-256: 32ba4b8453487590852e6955171e7c68535b558fe4fb878ccc1c124394375d22
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ x)) ◇ (z ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ y) ◇ x) ◇ y) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q1 ◇ (q1 ◇ q0)) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) ((h q1 q0 q0).symm))).symm).trans ((h q0 q1 ((q0 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q0))).symm)
  have apc4 : forall (q2 q3 q4:G), ((q3 ◇ (q4 ◇ ((q2 ◇ (q2 ◇ q3)) ◇ q2))) ◇ q3) = q3:=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q4 ◇ ((q2 ◇ (q2 ◇ q3)) ◇ q2))) (apc0 q3 q2))).symm).trans (((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q4 ◇ ((q2 ◇ (q2 ◇ q3)) ◇ q2))) (cg (fun t => ((q2 ◇ (q2 ◇ q3)) ◇ q2) ◇ t) (apc0 q3 q2)))).symm).trans ((h q3 ((q2 ◇ (q2 ◇ q3)) ◇ q2) q4).symm))
  have apc5 : forall (q5 q6:G), (q6 ◇ ((q5 ◇ (q5 ◇ q6)) ◇ q5)) = ((q5 ◇ (q5 ◇ q6)) ◇ q5):=by
    intro q5 q6
    exact ((cg (fun t => t ◇ ((q5 ◇ (q5 ◇ q6)) ◇ q5)) (apc4 q5 q6 q6)).symm).trans (apc0 ((q5 ◇ (q5 ◇ q6)) ◇ q5) q6)
  have apc10 : forall (q5 q7 q8:G), ((q8 ◇ (q8 ◇ (q7 ◇ ((q5 ◇ (q5 ◇ q8)) ◇ q5)))) ◇ q8) = q8:=by
    intro q5 q7 q8
    exact ((cg (fun t => t ◇ q8) (cg (fun t => t ◇ (q8 ◇ (q7 ◇ ((q5 ◇ (q5 ◇ q8)) ◇ q5)))) (apc4 q5 q8 q7))).symm).trans (((cg (fun t => t ◇ q8) (cg (fun t => t ◇ (q8 ◇ (q7 ◇ ((q5 ◇ (q5 ◇ q8)) ◇ q5)))) (cg (fun t => (q8 ◇ (q7 ◇ ((q5 ◇ (q5 ◇ q8)) ◇ q5))) ◇ t) (apc4 q5 q8 q7)))).symm).trans (apc0 q8 (q8 ◇ (q7 ◇ ((q5 ◇ (q5 ◇ q8)) ◇ q5)))))
  have apc11 : forall (q9 q10 q11:G), ((q10 ◇ ((q9 ◇ (q9 ◇ q11)) ◇ q9)) ◇ q11) = q11:=by
    intro q9 q10 q11
    exact (((cg (fun t => (q10 ◇ ((q9 ◇ (q9 ◇ q11)) ◇ q9)) ◇ t) (apc10 q9 q10 q11)).symm).trans (apc5 q11 (q10 ◇ ((q9 ◇ (q9 ◇ q11)) ◇ q9)))).trans (apc10 q9 q10 q11)
  have apc12 : forall (q12 q13 q14:G), (q14 ◇ (q13 ◇ ((q12 ◇ (q12 ◇ q14)) ◇ q12))) = (q13 ◇ ((q12 ◇ (q12 ◇ q14)) ◇ q12)):=by
    intro q12 q13 q14
    exact ((cg (fun t => t ◇ (q13 ◇ ((q12 ◇ (q12 ◇ q14)) ◇ q12))) (apc10 q12 q13 q14)).symm).trans (apc0 (q13 ◇ ((q12 ◇ (q12 ◇ q14)) ◇ q12)) q14)
  have apc13 : forall (q15 q16 q17:G), (((q15 ◇ (q15 ◇ q16)) ◇ q15) ◇ (q17 ◇ q16)) = (q17 ◇ q16):=by
    intro q15 q16 q17
    exact (((cg (fun t => ((q15 ◇ (q15 ◇ q16)) ◇ q15) ◇ t) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q16) (apc5 q15 q16)))).trans (cg (fun t => ((q15 ◇ (q15 ◇ q16)) ◇ q15) ◇ t) (cg (fun t => q17 ◇ t) (apc0 q16 q15)))).symm).trans ((((cg (fun t => ((q15 ◇ (q15 ◇ q16)) ◇ q15) ◇ t) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q16) (cg (fun t => q16 ◇ t) (apc5 q15 q16))))).symm).trans (apc12 q16 q17 ((q15 ◇ (q15 ◇ q16)) ◇ q15))).trans (((cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q16) (cg (fun t => q16 ◇ t) (apc5 q15 q16)))).trans (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q16) (apc5 q15 q16)))).trans (cg (fun t => q17 ◇ t) (apc0 q16 q15))))
  have apc14 : forall (q18 q19 q20:G), ((q20 ◇ q19) ◇ ((q18 ◇ (q18 ◇ q19)) ◇ q18)) = ((q18 ◇ (q18 ◇ q19)) ◇ q18):=by
    intro q18 q19 q20
    exact (((cg (fun t => t ◇ ((q18 ◇ (q18 ◇ q19)) ◇ q18)) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q19) (apc5 q18 q19)))).trans (cg (fun t => t ◇ ((q18 ◇ (q18 ◇ q19)) ◇ q18)) (cg (fun t => q20 ◇ t) (apc0 q19 q18)))).symm).trans (((cg (fun t => t ◇ ((q18 ◇ (q18 ◇ q19)) ◇ q18)) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q19) (cg (fun t => q19 ◇ t) (apc5 q18 q19))))).symm).trans (apc11 q19 q20 ((q18 ◇ (q18 ◇ q19)) ◇ q18)))
  have apc21 : forall (q21 q22 q23 q24:G), (((q21 ◇ (q21 ◇ q22)) ◇ q21) ◇ (q24 ◇ (q23 ◇ q22))) = (q24 ◇ (q23 ◇ q22)):=by
    intro q21 q22 q23 q24
    exact (((cg (fun t => ((q21 ◇ (q21 ◇ q22)) ◇ q21) ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ (q23 ◇ q22)) (apc14 q21 q22 q23)))).trans (cg (fun t => ((q21 ◇ (q21 ◇ q22)) ◇ q21) ◇ t) (cg (fun t => q24 ◇ t) (apc13 q21 q22 q23)))).symm).trans ((((cg (fun t => ((q21 ◇ (q21 ◇ q22)) ◇ q21) ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ (q23 ◇ q22)) (cg (fun t => (q23 ◇ q22) ◇ t) (apc14 q21 q22 q23))))).symm).trans (apc12 (q23 ◇ q22) q24 ((q21 ◇ (q21 ◇ q22)) ◇ q21))).trans (((cg (fun t => q24 ◇ t) (cg (fun t => t ◇ (q23 ◇ q22)) (cg (fun t => (q23 ◇ q22) ◇ t) (apc14 q21 q22 q23)))).trans (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ (q23 ◇ q22)) (apc14 q21 q22 q23)))).trans (cg (fun t => q24 ◇ t) (apc13 q21 q22 q23))))
  have apc27 : forall (q25 q26 q27 q28:G), ((q28 ◇ (q27 ◇ q26)) ◇ ((q25 ◇ (q25 ◇ q26)) ◇ q25)) = ((q25 ◇ (q25 ◇ q26)) ◇ q25):=by
    intro q25 q26 q27 q28
    exact (((cg (fun t => t ◇ ((q25 ◇ (q25 ◇ q26)) ◇ q25)) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ (q27 ◇ q26)) (apc14 q25 q26 q27)))).trans (cg (fun t => t ◇ ((q25 ◇ (q25 ◇ q26)) ◇ q25)) (cg (fun t => q28 ◇ t) (apc13 q25 q26 q27)))).symm).trans (((cg (fun t => t ◇ ((q25 ◇ (q25 ◇ q26)) ◇ q25)) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ (q27 ◇ q26)) (cg (fun t => (q27 ◇ q26) ◇ t) (apc14 q25 q26 q27))))).symm).trans (apc11 (q27 ◇ q26) q28 ((q25 ◇ (q25 ◇ q26)) ◇ q25)))
  have apc28 : forall (q29 q30:G), ((q30 ◇ (q30 ◇ q29)) ◇ q30) = q30:=by
    intro q29 q30
    exact ((cg (fun t => t ◇ q30) (apc21 q30 q29 q30 q30)).symm).trans (((cg (fun t => t ◇ q30) (cg (fun t => t ◇ (q30 ◇ (q30 ◇ q29))) (apc27 q30 q29 q30 q30))).symm).trans (apc0 q30 (q30 ◇ (q30 ◇ q29))))
  have apc29 : forall (q29 q30 q5 q6:G), (q6 ◇ q5) = q5:=by
    intro q29 q30 q5 q6
    exact ((cg (fun t => q6 ◇ t) (apc28 q6 q5)).symm).trans ((apc5 q5 q6).trans (apc28 q6 q5))
  exact ((apc29 x x x z).symm).trans ((apc29 x x (z ◇ x) (((y ◇ y) ◇ x) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35768_to_28744 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_35768_to_28744
