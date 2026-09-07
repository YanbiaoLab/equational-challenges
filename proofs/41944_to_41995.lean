-- Equation41944 → Equation41995
-- Recorded verdict: true
-- Premise: x * y = y * (y * (z * (y * x)))
-- Conclusion: x * y = y * (z * (z * (y * x)))
-- Original submission SHA-256: e773bf1a4524c3f7643521f14737c00861b99bb9810f016125a352a4dea778db
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ (z ◇ (y ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ (z ◇ (y ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = ((q1 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) ((h q0 q1 q1).symm)).symm).trans ((h (q1 ◇ q0) q1 q1).symm)
  have apc5 : forall (q2 q3:G), (q3 ◇ (q3 ◇ ((q2 ◇ q3) ◇ q2))) = (q2 ◇ q3):=by
    intro q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (apc0 q3 q2))).symm).trans ((h q2 q3 q2).symm)
  have apc6 : forall (q4 q5:G), ((q5 ◇ q4) ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((apc5 (q5 ◇ q4) q5).symm).trans ((h q4 q5 ((q5 ◇ q4) ◇ q5)).symm)
  have apc8 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = (q0 ◇ q1):=by
    intro q0 q1
    exact (apc0 q0 q1).trans (apc6 q0 q1)
  have apc9 : forall (q6 q7:G), ((q6 ◇ q7) ◇ (q6 ◇ q7)) = (q6 ◇ q7):=by
    intro q6 q7
    exact (((cg (fun t => (q6 ◇ q7) ◇ t) (apc8 q6 q7)).symm).trans (apc8 q7 (q6 ◇ q7))).trans (apc8 q6 q7)
  have apc10 : forall (q8 q9 q10:G), (q10 ◇ (q8 ◇ q9)) = (q8 ◇ q9):=by
    intro q8 q9 q10
    exact (((cg (fun t => (q8 ◇ q9) ◇ t) (apc8 q10 (q8 ◇ q9))).trans (apc8 q10 (q8 ◇ q9))).symm).trans ((((cg (fun t => (q8 ◇ q9) ◇ t) (cg (fun t => (q8 ◇ q9) ◇ t) (cg (fun t => q10 ◇ t) (apc9 q8 q9)))).symm).trans ((h (q8 ◇ q9) (q8 ◇ q9) q10).symm)).trans (apc9 q8 q9))
  have apc11 : forall (q11 q12 q13:G), (q12 ◇ q11) = (q11 ◇ q12):=by
    intro q11 q12 q13
    exact (((cg (fun t => q12 ◇ t) (apc10 q12 q11 q13)).trans (apc10 q12 q11 q12)).symm).trans (((apc10 q12 (q13 ◇ (q12 ◇ q11)) q12).symm).trans ((h q11 q12 q13).symm))
  have apc12 : forall (q14 q15 q12 q13:G), ((((q14 ◇ q15) ◇ q13) ◇ q12) ◇ q12) = ((q14 ◇ q15) ◇ q12):=by
    intro q14 q15 q12 q13
    exact ((((cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (apc11 (q14 ◇ q15) q13 (q13 ◇ (q14 ◇ q15))))).trans (cg (fun t => q12 ◇ t) (apc11 ((q14 ◇ q15) ◇ q13) q12 (q12 ◇ ((q14 ◇ q15) ◇ q13))))).trans (apc11 (((q14 ◇ q15) ◇ q13) ◇ q12) q12 (q12 ◇ (((q14 ◇ q15) ◇ q13) ◇ q12)))).symm).trans (((cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (cg (fun t => q13 ◇ t) (apc10 q14 q15 q12)))).symm).trans ((h (q14 ◇ q15) q12 q13).symm))
  have apc14 : forall (q16 q17 q18 q19:G), ((q16 ◇ q17) ◇ q19) = (q18 ◇ q19):=by
    intro q16 q17 q18 q19
    exact (((((cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => (q16 ◇ q17) ◇ t) (apc11 q18 q19 (q19 ◇ q18))))).trans (cg (fun t => q19 ◇ t) (apc11 ((q16 ◇ q17) ◇ (q18 ◇ q19)) q19 (q19 ◇ ((q16 ◇ q17) ◇ (q18 ◇ q19)))))).trans (apc11 (((q16 ◇ q17) ◇ (q18 ◇ q19)) ◇ q19) q19 (q19 ◇ (((q16 ◇ q17) ◇ (q18 ◇ q19)) ◇ q19)))).trans (apc12 q16 q17 q19 (q18 ◇ q19))).symm).trans (((cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (apc12 q16 q17 (q19 ◇ q18) q16))).symm).trans ((h q18 q19 (((q16 ◇ q17) ◇ q16) ◇ (q19 ◇ q18))).symm))
  have apc15 : forall (q16 q18 q19 q17:G), (q18 ◇ q19) = (q16 ◇ q19):=by
    intro q16 q18 q19 q17
    exact ((apc14 q16 q17 q18 q19).symm).trans (apc14 q16 q17 q16 q19)
  have apc16 : forall (q20 q21 q22:G), (q21 ◇ q22) = (q20 ◇ q21):=by
    intro q20 q21 q22
    exact (((apc15 q20 q22 q21 q20).symm).trans (apc11 q21 q22 q20)).symm
  exact (apc16 (z ◇ (z ◇ (y ◇ x))) x y).trans (apc16 y (z ◇ (z ◇ (y ◇ x))) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41944_to_41995 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41944_to_41995
