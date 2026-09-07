-- Equation45411 → Equation53836
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (((x ◇ z) ◇ x) ◇ x)
-- Conclusion: x ◇ (x ◇ x) = y ◇ (y ◇ (y ◇ y))
-- Original submission SHA-256: 754509ca8d59f38ba285be45962fce9feface50298b8c25d320e62a31a04e86b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (((x ◇ z) ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = y ◇ (y ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) ((h q0 q1 q0).symm)))).symm).trans ((h q1 q2 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q6 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q5)))) = ((((q3 ◇ q4) ◇ q4) ◇ q4) ◇ q6):=by
    intro q3 q4 q5 q6
    exact (((cg (fun t => q6 ◇ t) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (((q3 ◇ q4) ◇ q4) ◇ q4)) (apc0 q3 q4 q5)))).trans (cg (fun t => q6 ◇ t) (cg (fun t => q4 ◇ t) (apc0 q3 q4 (q4 ◇ q5))))).symm).trans (((cg (fun t => q6 ◇ t) (apc0 q3 q4 ((q5 ◇ (((q3 ◇ q4) ◇ q4) ◇ q4)) ◇ (((q3 ◇ q4) ◇ q4) ◇ q4)))).symm).trans (apc0 q5 (((q3 ◇ q4) ◇ q4) ◇ q4) q6))
  have apc2 : forall (q7 q8 q9:G), (q9 ◇ (q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q7))))) = (q8 ◇ q9):=by
    intro q7 q8 q9
    exact ((cg (fun t => q9 ◇ t) ((apc1 q7 q8 q7 q8).symm)).symm).trans (apc0 (q7 ◇ q8) q8 q9)
  have apc5 : forall (q10 q11:G), (q11 ◇ (q10 ◇ q10)) = (q10 ◇ q11):=by
    intro q10 q11
    exact ((cg (fun t => q11 ◇ t) (apc2 q10 q10 q10)).symm).trans (apc2 (q10 ◇ q10) q10 q11)
  have apc11 : forall (q12 q13:G), ((q12 ◇ q12) ◇ q13) = (q12 ◇ q13):=by
    intro q12 q13
    exact ((((cg (fun t => q13 ◇ t) (apc5 q12 q12)).trans (apc5 q12 q13)).symm).trans (((cg (fun t => q13 ◇ t) (apc5 q12 (q12 ◇ q12))).symm).trans (apc5 (q12 ◇ q12) q13))).symm
  have apc12 : forall (q14 q15:G), (q15 ◇ q14) = (q14 ◇ q15):=by
    intro q14 q15
    exact ((apc5 q15 q14).symm).trans ((((apc11 q14 (q15 ◇ q15)).symm).trans (apc5 q15 (q14 ◇ q14))).trans (apc5 q14 q15))
  have apc17 : forall (q16 q17 q18:G), ((((q16 ◇ q17) ◇ q17) ◇ q17) ◇ q18) = (q17 ◇ q18):=by
    intro q16 q17 q18
    exact ((((((cg (fun t => q18 ◇ t) (apc12 (q17 ◇ q17) q17)).trans (cg (fun t => q18 ◇ t) (apc11 q17 q17))).trans (apc12 (q17 ◇ q17) q18)).trans (apc11 q17 q18)).symm).trans (((cg (fun t => q18 ◇ t) (cg (fun t => q17 ◇ t) (apc2 q16 q17 q17))).symm).trans (apc1 q16 q17 (q17 ◇ (q17 ◇ (q17 ◇ q16))) q18))).symm
  have apc19 : forall (q19 q20 q21:G), (((q19 ◇ q21) ◇ q21) ◇ q20) = (q20 ◇ q21):=by
    intro q19 q20 q21
    exact ((((((((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ ((q19 ◇ q21) ◇ q21)) (apc12 ((q19 ◇ q21) ◇ q21) q21))).trans (cg (fun t => q20 ◇ t) (apc17 q19 q21 ((q19 ◇ q21) ◇ q21)))).trans (cg (fun t => q20 ◇ t) (apc12 ((q19 ◇ q21) ◇ q21) q21))).trans (apc12 (((q19 ◇ q21) ◇ q21) ◇ q21) q20)).trans (apc17 q19 q21 q20)).trans (apc12 q20 q21)).symm).trans (((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ ((q19 ◇ q21) ◇ q21)) (apc17 q19 q21 ((q19 ◇ q21) ◇ q21)))).symm).trans ((h ((q19 ◇ q21) ◇ q21) q20 q21).symm))).symm
  have apc20 : forall (q22 q23 q24:G), ((q22 ◇ q24) ◇ q23) = (q23 ◇ q24):=by
    intro q22 q23 q24
    exact (((((cg (fun t => q23 ◇ t) (apc19 q22 (q22 ◇ q24) q24)).trans (apc12 ((q22 ◇ q24) ◇ q24) q23)).trans (apc19 q22 q23 q24)).symm).trans (((cg (fun t => q23 ◇ t) (cg (fun t => t ◇ (q22 ◇ q24)) (apc19 q22 (q22 ◇ q24) q24))).symm).trans ((h (q22 ◇ q24) q23 q24).symm))).symm
  have apc22 : forall (q25 q26 q27:G), (q26 ◇ q27) = (q25 ◇ q26):=by
    intro q25 q26 q27
    exact ((((cg (fun t => q26 ◇ t) (apc20 q25 q25 q27)).trans (apc12 (q25 ◇ q27) q26)).trans (apc20 q25 q26 q27)).symm).trans (((cg (fun t => q26 ◇ t) (cg (fun t => t ◇ q25) (apc20 q25 q25 q27))).symm).trans ((h q25 q26 q27).symm))
  exact (apc22 (y ◇ (y ◇ y)) x (x ◇ x)).trans (apc22 y (y ◇ (y ◇ y)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45411_to_53836 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45411_to_53836
