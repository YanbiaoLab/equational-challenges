-- Equation22454 → Equation27665
-- Recorded verdict: true
-- Premise: x = (y * (x * x)) * ((y * z) * x)
-- Conclusion: x = ((x * (y * z)) * z) * (z * x)
-- Original submission SHA-256: 9d7ea0d0b0c4694025e0d9c7bdc3d033428ea4b5e3aff4c5076dd8ed6f723190
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ x)) ◇ ((y ◇ z) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ (y ◇ z)) ◇ z) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ ((q2 ◇ q1) ◇ q0))) ◇ q0) = ((q2 ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ ((q2 ◇ q1) ◇ q0))) ◇ t) ((h q0 q2 q1).symm)).symm).trans ((h ((q2 ◇ q1) ◇ q0) q2 (q0 ◇ q0)).symm)
  have apc3 : forall (q0 q3 q4:G), (((q3 ◇ (q0 ◇ q0)) ◇ (q4 ◇ q4)) ◇ (q0 ◇ q4)) = q4:=by
    intro q0 q3 q4
    exact ((cg (fun t => ((q3 ◇ (q0 ◇ q0)) ◇ (q4 ◇ q4)) ◇ t) (cg (fun t => t ◇ q4) ((h q0 q3 q0).symm))).symm).trans ((h q4 (q3 ◇ (q0 ◇ q0)) ((q3 ◇ q0) ◇ q0)).symm)
  have apc4 : forall (q5:G), (q5 ◇ (q5 ◇ q5)) = q5:=by
    intro q5
    exact ((cg (fun t => t ◇ (q5 ◇ q5)) (apc3 q5 q5 q5)).symm).trans (apc3 q5 (q5 ◇ (q5 ◇ q5)) q5)
  have apc9 : forall (q6 q7:G), ((q7 ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) = (q7 ◇ q6):=by
    intro q6 q7
    exact ((cg (fun t => t ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) (cg (fun t => q7 ◇ t) (cg (fun t => (q7 ◇ q6) ◇ t) (apc4 (q7 ◇ q6))))).symm).trans ((((cg (fun t => t ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) (cg (fun t => q7 ◇ t) (cg (fun t => t ◇ ((q7 ◇ q6) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6)))) (apc4 (q7 ◇ q6))))).symm).trans (apc0 ((q7 ◇ q6) ◇ (q7 ◇ q6)) q6 q7)).trans (apc4 (q7 ◇ q6)))
  have apc10 : forall (q8 q7:G), ((q7 ◇ ((q7 ◇ q8) ◇ (q7 ◇ q8))) ◇ q8) = (q7 ◇ q8):=by
    intro q8 q7
    exact ((cg (fun t => t ◇ q8) (cg (fun t => q7 ◇ t) (cg (fun t => (q7 ◇ q8) ◇ t) (cg (fun t => t ◇ q8) (apc4 q7))))).symm).trans ((((cg (fun t => t ◇ q8) (cg (fun t => q7 ◇ t) (cg (fun t => t ◇ ((q7 ◇ (q7 ◇ q7)) ◇ q8)) (cg (fun t => t ◇ q8) (apc4 q7))))).symm).trans (apc0 q8 (q7 ◇ q7) q7)).trans (cg (fun t => t ◇ q8) (apc4 q7)))
  have apc11 : forall (q9 q10:G), ((q9 ◇ q10) ◇ q10) = (q9 ◇ q10):=by
    intro q9 q10
    exact (((cg (fun t => t ◇ q10) (cg (fun t => (q9 ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))) ◇ t) (cg (fun t => (q9 ◇ q10) ◇ t) (apc10 q10 q9)))).trans (cg (fun t => t ◇ q10) (apc9 q10 q9))).symm).trans ((((cg (fun t => t ◇ q10) (cg (fun t => (q9 ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))) ◇ t) (cg (fun t => t ◇ ((q9 ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))) ◇ q10)) (apc10 q10 q9)))).symm).trans (apc10 q10 (q9 ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))))).trans (apc10 q10 q9))
  have apc12 : forall (q11 q12:G), (q12 ◇ (q11 ◇ q11)) = q11:=by
    intro q11 q12
    exact ((apc11 q12 (q11 ◇ q11)).symm).trans (((apc11 (q12 ◇ (q11 ◇ q11)) (q11 ◇ q11)).symm).trans (apc3 q11 q12 q11))
  have apc13 : forall (q13 q14:G), (q14 ◇ q13) = (q13 ◇ q13):=by
    intro q13 q14
    exact ((cg (fun t => q14 ◇ t) (apc12 q13 (q13 ◇ q13))).symm).trans (apc12 (q13 ◇ q13) q14)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (y ◇ z)) ◇ z) ◇ (z ◇ x)):=(((cg (fun t => ((x ◇ (y ◇ z)) ◇ z) ◇ t) (apc13 x z)).trans (cg (fun t => t ◇ (x ◇ x)) (apc13 z (x ◇ (y ◇ z))))).trans (apc12 x (z ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22454_to_27665 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22454_to_27665
