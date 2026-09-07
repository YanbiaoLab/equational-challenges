-- Equation12028 → Equation4608
-- Recorded verdict: true
-- Premise: x = y ◇ (((x ◇ z) ◇ z) ◇ (y ◇ z))
-- Conclusion: (x ◇ x) ◇ y = (y ◇ y) ◇ x
-- Original submission SHA-256: bb9fcfe0febfb5379b0d127f8fba46373f5e89839fdbd5ee766ae46c07c43192
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ z) ◇ z) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = (y ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (((x ◇ z) ◇ z) ◇ (y ◇ z))) = (x ◇ (((x ◇ x) ◇ x) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (x ◇ (((x ◇ x) ◇ x) ◇ (x ◇ x))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q1 ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)))) (apc1 q0 (q0 ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) (q0 ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)))))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) (apc1 q0 q0 q0)))).symm).trans ((h q0 q1 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))).symm))
  have apc3 : forall (q2:G), (q2 ◇ (q2 ◇ q2)) = q2:=by
    intro q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q2 q2 q2).symm))).symm).trans (apc2 q2 q2)
  have apc4 : forall (q3 q4:G), (q4 ◇ (q3 ◇ (q4 ◇ (q3 ◇ q3)))) = q3:=by
    intro q3 q4
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q4 ◇ (q3 ◇ q3))) (apc3 q3))).symm).trans (((cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q4 ◇ (q3 ◇ q3))) (cg (fun t => t ◇ (q3 ◇ q3)) (apc3 q3)))).symm).trans ((h q3 q4 (q3 ◇ q3)).symm))
  have apc5 : forall (q5 q6:G), (((q5 ◇ q6) ◇ q6) ◇ q5) = q6:=by
    intro q5 q6
    exact ((cg (fun t => ((q5 ◇ q6) ◇ q6) ◇ t) ((h q5 q6 q6).symm)).symm).trans (apc4 q6 ((q5 ◇ q6) ◇ q6))
  have apc6 : forall (q7 q8:G), (q7 ◇ (q8 ◇ (q7 ◇ q8))) = (q8 ◇ q8):=by
    intro q7 q8
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ (q7 ◇ q8)) (apc5 q8 q8))).symm).trans ((h (q8 ◇ q8) q7 q8).symm)
  have apc10 : forall (q9 q7 q8:G), (q7 ◇ ((q9 ◇ q8) ◇ (q7 ◇ q8))) = ((q8 ◇ q9) ◇ q9):=by
    intro q9 q7 q8
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ (q7 ◇ q8)) (cg (fun t => t ◇ q8) (apc5 q8 q9)))).symm).trans ((h ((q8 ◇ q9) ◇ q9) q7 q8).symm)
  have apc11 : forall (x y z q9 q7 q8:G), ((z ◇ (x ◇ z)) ◇ (x ◇ z)) = x:=by
    intro x y z q9 q7 q8
    exact ((h x x z).trans (apc10 (x ◇ z) x z)).symm
  have apc12 : forall (q10 q11:G), (((q10 ◇ q11) ◇ q10) ◇ q10) = (q11 ◇ (q10 ◇ q11)):=by
    intro q10 q11
    exact ((apc10 q10 q10 (q10 ◇ q11)).symm).trans (((cg (fun t => q10 ◇ t) (cg (fun t => t ◇ (q10 ◇ (q10 ◇ q11))) (cg (fun t => t ◇ (q10 ◇ q11)) (apc11 q10 q10 q11 q10 q10 q10)))).symm).trans ((h (q11 ◇ (q10 ◇ q11)) q10 (q10 ◇ q11)).symm))
  have apc14 : forall (q10 q12 q13:G), (q13 ◇ (q10 ◇ (q13 ◇ (q10 ◇ q12)))) = q12:=by
    intro q10 q12 q13
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ (q13 ◇ (q10 ◇ q12))) (apc11 q10 q10 q12 q10 q10 q10))).symm).trans ((h q12 q13 (q10 ◇ q12)).symm)
  have apc18 : forall (q14 q15:G), ((q15 ◇ (q14 ◇ q15)) ◇ (q14 ◇ q14)) = q15:=by
    intro q14 q15
    exact ((cg (fun t => (q15 ◇ (q14 ◇ q15)) ◇ t) (cg (fun t => q14 ◇ t) (apc11 q14 q14 q15 q14 q14 q14))).symm).trans (apc14 q14 q15 (q15 ◇ (q14 ◇ q15)))
  have apc19 : forall (q16 q17:G), (((q16 ◇ q16) ◇ q17) ◇ q17) = (q17 ◇ (q16 ◇ q17)):=by
    intro q16 q17
    exact ((apc10 q17 q16 (q16 ◇ q16)).symm).trans (((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ (q16 ◇ (q16 ◇ q16))) (cg (fun t => t ◇ (q16 ◇ q16)) (apc18 q16 q17)))).symm).trans ((h (q17 ◇ (q16 ◇ q17)) q16 (q16 ◇ q16)).symm))
  have apc23 : forall (q18 q19:G), (((q19 ◇ q18) ◇ q19) ◇ (q18 ◇ q18)) = (q19 ◇ q19):=by
    intro q18 q19
    exact ((cg (fun t => ((q19 ◇ q18) ◇ q19) ◇ t) (apc6 q19 q18)).symm).trans (((cg (fun t => ((q19 ◇ q18) ◇ q19) ◇ t) (cg (fun t => q19 ◇ t) (apc12 q19 q18))).symm).trans (apc6 ((q19 ◇ q18) ◇ q19) q19))
  have apc53 : forall (q20 q21:G), ((q21 ◇ q21) ◇ (q20 ◇ (q21 ◇ q21))) = ((q21 ◇ q20) ◇ q21):=by
    intro q20 q21
    exact (((apc10 (q21 ◇ q21) q20 (q20 ◇ q20)).trans (apc19 q20 (q21 ◇ q21))).symm).trans (((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ (q20 ◇ (q20 ◇ q20))) (cg (fun t => t ◇ (q20 ◇ q20)) (apc23 q20 q21)))).symm).trans ((h ((q21 ◇ q20) ◇ q21) q20 (q20 ◇ q20)).symm))
  have apc54 : forall (q22 q23:G), ((q23 ◇ q23) ◇ q22) = ((q22 ◇ q22) ◇ q23):=by
    intro q22 q23
    exact (((cg (fun t => (q23 ◇ q23) ◇ t) (apc5 (q23 ◇ q23) q22)).symm).trans (apc53 (((q23 ◇ q23) ◇ q22) ◇ q22) q23)).trans ((cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc19 q23 q22))).trans (cg (fun t => t ◇ q23) (apc6 q23 q22)))
  exact apc54 y x

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_12028_to_4608 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_12028_to_4608
