-- Equation41888 → Equation326
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (x ◇ (y ◇ z)))
-- Conclusion: x ◇ y = x ◇ (y ◇ y)
-- Original submission SHA-256: 5570deaecfa2d7f95859e0380e426a9e60d96659c0f21f2f15be56b8885f1261
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (x ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = x ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) ((h q0 q0 q0).symm)).symm).trans ((h q0 q0 (q0 ◇ q0)).symm)
  have apc1 : forall (q1 q0:G), (q0 ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ q0):=by
    intro q1 q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) ((h q0 q1 q1).symm))).symm).trans ((h q1 q0 (q0 ◇ (q1 ◇ q1))).symm)
  have apc2 : forall (q2 q1 q0:G), (q0 ◇ (q1 ◇ (q1 ◇ (q2 ◇ q0)))) = (q1 ◇ q0):=by
    intro q2 q1 q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) ((h q2 q0 q2).symm)))).symm).trans ((h q1 q0 (q2 ◇ (q2 ◇ (q0 ◇ q2)))).symm)
  have apc3 : forall (q3 q4:G), ((q3 ◇ q4) ◇ (q4 ◇ q4)) = (q4 ◇ (q3 ◇ q4)):=by
    intro q3 q4
    exact ((cg (fun t => (q3 ◇ q4) ◇ t) (apc2 q3 q4 q4)).symm).trans (apc2 q4 q4 (q3 ◇ q4))
  have apc7 : forall (q5 q6:G), ((q6 ◇ q5) ◇ (q6 ◇ q6)) = (q6 ◇ (q6 ◇ q5)):=by
    intro q5 q6
    exact ((cg (fun t => (q6 ◇ q5) ◇ t) ((h q6 q6 q5).symm)).symm).trans (apc2 q6 q6 (q6 ◇ q5))
  have apc16 : forall (q7 q8:G), ((q8 ◇ q8) ◇ (q8 ◇ (q8 ◇ q7))) = (q8 ◇ (q8 ◇ (q8 ◇ q7))):=by
    intro q7 q8
    exact (((((cg (fun t => (q8 ◇ (q8 ◇ q7)) ◇ t) (apc3 q8 q8)).trans (cg (fun t => (q8 ◇ (q8 ◇ q7)) ◇ t) (apc0 q8))).trans (apc7 (q8 ◇ q7) q8)).symm).trans ((((cg (fun t => t ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) (apc7 q7 q8)).symm).trans (apc3 (q8 ◇ q7) (q8 ◇ q8))).trans (cg (fun t => (q8 ◇ q8) ◇ t) (apc7 q7 q8)))).symm
  have apc17 : forall (q9 q10:G), ((q10 ◇ q10) ◇ (q10 ◇ q9)) = (q10 ◇ (q10 ◇ q9)):=by
    intro q9 q10
    exact ((((cg (fun t => (q10 ◇ q9) ◇ t) (apc16 (q10 ◇ q9) q10)).trans (apc2 q10 q10 (q10 ◇ q9))).symm).trans (((cg (fun t => (q10 ◇ q9) ◇ t) (cg (fun t => (q10 ◇ q10) ◇ t) (apc16 q9 q10))).symm).trans (apc2 q10 (q10 ◇ q10) (q10 ◇ q9)))).symm
  have apc18 : forall (q11 q12:G), ((q11 ◇ q11) ◇ q12) = (q11 ◇ q12):=by
    intro q11 q12
    exact ((((cg (fun t => q12 ◇ t) (apc17 (q11 ◇ q12) q11)).trans (apc2 q11 q11 q12)).symm).trans (((cg (fun t => q12 ◇ t) (cg (fun t => (q11 ◇ q11) ◇ t) (apc17 q12 q11))).symm).trans (apc2 q11 (q11 ◇ q11) q12))).symm
  have apc19 : forall (q13 q14:G), (q14 ◇ (q13 ◇ q13)) = (q14 ◇ q13):=by
    intro q13 q14
    exact ((((cg (fun t => q13 ◇ t) (cg (fun t => q14 ◇ t) (apc18 q13 q14))).trans (apc1 q14 q13)).symm).trans (((apc18 q13 (q14 ◇ ((q13 ◇ q13) ◇ q14))).symm).trans (apc1 q14 (q13 ◇ q13)))).symm
  exact (apc19 y x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41888_to_326 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41888_to_326
