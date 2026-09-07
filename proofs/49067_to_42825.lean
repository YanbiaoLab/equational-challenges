-- Equation49067 → Equation42825
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * y) * (x * x)
-- Conclusion: x * y = y * (y * ((z * z) * x))
-- Original submission SHA-256: f0d309242ba9a3c4054a9a87b9498a4f93f931b29a07f48da2100ba3ee71d1f2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ y) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ ((z ◇ z) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) ((h q0 q1 q0).symm)).symm).trans ((h q1 (q0 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ ((q3 ◇ q2) ◇ (q3 ◇ q2))) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((apc0 (q3 ◇ q2) q2).symm).trans ((h q2 q2 q3).symm)
  have apc2 : forall (q4:G), (q4 ◇ (q4 ◇ (q4 ◇ q4))) = (q4 ◇ q4):=by
    intro q4
    exact ((cg (fun t => q4 ◇ t) (apc0 q4 q4)).symm).trans (apc1 q4 q4)
  have apc3 : forall (q2 q3:G), ((q2 ◇ (q3 ◇ q3)) ◇ (q2 ◇ q2)) = (q2 ◇ (q2 ◇ q2)):=by
    intro q2 q3
    exact ((cg (fun t => t ◇ (q2 ◇ q2)) (apc0 q3 q2)).symm).trans ((h q2 (q2 ◇ q2) q3).symm)
  have apc4 : forall (x y z:G), (((z ◇ x) ◇ y) ◇ (x ◇ x)) = (((x ◇ x) ◇ y) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc5 : forall (q5 q6:G), (((q5 ◇ q5) ◇ q6) ◇ (q5 ◇ q5)) = (q5 ◇ q6):=by
    intro q5 q6
    exact ((apc4 q5 q6 q5).symm).trans ((h q5 q6 q5).symm)
  have apc7 : forall (q7:G), ((q7 ◇ (q7 ◇ q7)) ◇ (q7 ◇ (q7 ◇ q7))) = (q7 ◇ (q7 ◇ q7)):=by
    intro q7
    exact ((cg (fun t => (q7 ◇ (q7 ◇ q7)) ◇ t) (apc0 q7 q7)).symm).trans ((((cg (fun t => t ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) (apc5 q7 (q7 ◇ q7))).symm).trans (apc5 (q7 ◇ q7) (q7 ◇ q7))).trans (apc0 q7 q7))
  have apc8 : forall (q8:G), ((q8 ◇ q8) ◇ (q8 ◇ (q8 ◇ q8))) = (q8 ◇ (q8 ◇ q8)):=by
    intro q8
    exact (((cg (fun t => (q8 ◇ q8) ◇ t) (apc7 q8)).symm).trans (apc1 (q8 ◇ q8) q8)).trans (apc0 q8 q8)
  have apc9 : forall (q9:G), (q9 ◇ (q9 ◇ q9)) = (q9 ◇ q9):=by
    intro q9
    exact ((apc3 q9 q9).symm).trans ((((cg (fun t => t ◇ (q9 ◇ q9)) (apc8 q9)).symm).trans ((h q9 (q9 ◇ (q9 ◇ q9)) q9).symm)).trans (apc2 q9))
  have apc10 : forall (q10 q11:G), ((q11 ◇ q11) ◇ q10) = (q11 ◇ q10):=by
    intro q10 q11
    exact (((((cg (fun t => ((q11 ◇ q11) ◇ q10) ◇ t) (apc0 q11 q11)).trans (cg (fun t => ((q11 ◇ q11) ◇ q10) ◇ t) (apc9 q11))).trans (apc5 q11 q10)).symm).trans (((cg (fun t => t ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (cg (fun t => t ◇ q10) (apc9 q11))).symm).trans ((h (q11 ◇ q11) q10 q11).symm))).symm
  have apc11 : forall (q10 q11 q5 q6:G), ((q5 ◇ q6) ◇ (q5 ◇ q5)) = (q5 ◇ q6):=by
    intro q10 q11 q5 q6
    exact ((cg (fun t => t ◇ (q5 ◇ q5)) (apc10 q6 q5)).symm).trans (apc5 q5 q6)
  have apc12 : forall (q12 q13:G), (q12 ◇ ((q12 ◇ q13) ◇ (q12 ◇ q13))) = (q12 ◇ q13):=by
    intro q12 q13
    exact (((((cg (fun t => (q12 ◇ q13) ◇ t) (apc0 q12 q12)).trans (cg (fun t => (q12 ◇ q13) ◇ t) (apc9 q12))).trans (apc11 ((q12 ◇ q13) ◇ (q12 ◇ q12)) ((q12 ◇ q13) ◇ (q12 ◇ q12)) q12 q13)).symm).trans ((((cg (fun t => t ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) (apc11 q12 q12 q12 q13)).symm).trans (apc0 (q12 ◇ q13) (q12 ◇ q12))).trans (apc10 ((q12 ◇ q13) ◇ (q12 ◇ q13)) q12))).symm
  have apc13 : forall (q14 q15 q16:G), (((q15 ◇ (q14 ◇ q14)) ◇ q16) ◇ (q15 ◇ q15)) = (q15 ◇ q16):=by
    intro q14 q15 q16
    exact (((cg (fun t => ((q15 ◇ (q14 ◇ q14)) ◇ q16) ◇ t) (apc0 q15 q15)).trans (cg (fun t => ((q15 ◇ (q14 ◇ q14)) ◇ q16) ◇ t) (apc9 q15))).symm).trans ((((cg (fun t => t ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) (cg (fun t => t ◇ q16) (apc0 q14 q15))).symm).trans ((h (q15 ◇ q15) q16 (q14 ◇ q15)).symm)).trans (apc10 q16 q15))
  have apc14 : forall (q17 q18 q19:G), (q17 ◇ q18) = (q17 ◇ q17):=by
    intro q17 q18 q19
    exact ((((cg (fun t => (q17 ◇ q17) ◇ t) (cg (fun t => (q17 ◇ q18) ◇ t) (apc13 q19 q17 q18))).trans (apc10 ((q17 ◇ q18) ◇ (q17 ◇ q18)) q17)).trans (apc12 q17 q18)).symm).trans ((((cg (fun t => (q17 ◇ q17) ◇ t) (cg (fun t => t ◇ (((q17 ◇ (q19 ◇ q19)) ◇ q18) ◇ (q17 ◇ q17))) (apc13 q19 q17 q18))).symm).trans (apc1 (q17 ◇ q17) ((q17 ◇ (q19 ◇ q19)) ◇ q18))).trans ((apc0 q17 q17).trans (apc9 q17)))
  have apc15 : forall (q0 q1 q19 q17 q18:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q19 q17 q18
    exact ((((apc10 (q0 ◇ q0) q0).trans (apc14 q0 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)))).symm).trans ((((cg (fun t => t ◇ (q1 ◇ q1)) (apc14 q0 q1 (q0 ◇ q1))).trans (apc14 (q0 ◇ q0) (q1 ◇ q1) ((q0 ◇ q0) ◇ (q1 ◇ q1)))).symm).trans ((apc0 q0 q1).trans (apc14 q1 (q0 ◇ q0) (q1 ◇ (q0 ◇ q0)))))).symm
  have apc17 : forall (q20 q21 q22:G), (q22 ◇ q21) = (q20 ◇ q20):=by
    intro q20 q21 q22
    exact ((((apc10 q21 q20).trans (apc14 q20 q21 (q20 ◇ q21))).symm).trans (((cg (fun t => t ◇ q21) (apc15 q20 q22 q20 q20 q20)).symm).trans (apc10 q21 q22))).symm
  exact (apc17 (x ◇ y) y x).trans ((apc17 (x ◇ y) (y ◇ ((z ◇ z) ◇ x)) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49067_to_42825 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49067_to_42825
