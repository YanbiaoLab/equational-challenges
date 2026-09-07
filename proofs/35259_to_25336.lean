-- Equation35259 → Equation25336
-- Recorded verdict: true
-- Premise: x = ((y * z) * ((w * x) * z)) * x
-- Conclusion: x = (y * (y * (z * z))) * (z * x)
-- Original submission SHA-256: 1a8b82ee933eaad1662592ff207da7f5427c1e73f3becc55efb48fd7ab792131
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ ((w ◇ x) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ (z ◇ z))) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ ((q0 ◇ q1) ◇ q2)) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q2)) ((h q2 q0 q0 q0).symm))).symm).trans ((h q1 ((q0 ◇ q0) ◇ ((q0 ◇ q2) ◇ q0)) q2 q0).symm)
  have apc1 : forall (q3 q4:G), ((q4 ◇ (q3 ◇ q4)) ◇ q3) = q3:=by
    intro q3 q4
    exact ((cg (fun t => t ◇ q3) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q4) (apc0 q3 q3 q3)))).symm).trans (apc0 (q3 ◇ ((q3 ◇ q3) ◇ q3)) q3 q4)
  have apc2 : forall (q5 q6:G), ((q6 ◇ q6) ◇ (q6 ◇ q5)) = (q6 ◇ q5):=by
    intro q5 q6
    exact ((cg (fun t => t ◇ (q6 ◇ q5)) (cg (fun t => q6 ◇ t) (apc1 q6 q5))).symm).trans (apc0 q5 (q6 ◇ q5) q6)
  have apc3 : forall (q1 q7 q2:G), (((q7 ◇ q2) ◇ (q1 ◇ q2)) ◇ q1) = q1:=by
    intro q1 q7 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => (q7 ◇ q2) ◇ t) (cg (fun t => t ◇ q2) ((h q1 q1 q1 q1).symm)))).symm).trans ((h q1 q7 q2 ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))).symm)
  have apc4 : forall (q8:G), ((q8 ◇ q8) ◇ q8) = q8:=by
    intro q8
    exact ((cg (fun t => t ◇ q8) (apc2 q8 q8)).symm).trans (apc3 q8 q8 q8)
  have apc5 : forall (x y z w:G), (((y ◇ z) ◇ ((w ◇ x) ◇ z)) ◇ x) = (x ◇ x):=by
    intro x y z w
    exact (((h x y z w).symm).trans (h x x x x)).trans ((cg (fun t => t ◇ x) (cg (fun t => (x ◇ x) ◇ t) (apc4 x))).trans (cg (fun t => t ◇ x) (apc4 x)))
  have apc6 : forall (q9 q10 q11:G), (q9 ◇ q9) = q9:=by
    intro q9 q10 q11
    exact (((apc0 q10 q9 q11).symm).trans (((cg (fun t => t ◇ q9) (cg (fun t => t ◇ ((q10 ◇ q9) ◇ q11)) (apc1 q11 q10))).symm).trans (apc5 q9 (q10 ◇ (q11 ◇ q10)) q11 q10))).symm
  have apc8 : forall (q12 q13:G), ((q12 ◇ q13) ◇ q12) = q12:=by
    intro q12 q13
    exact ((cg (fun t => t ◇ q12) (apc6 (q12 ◇ q13) q12 q12)).symm).trans (apc3 q12 q12 q13)
  have apc9 : forall (q14 q15:G), (q15 ◇ q14) = q14:=by
    intro q14 q15
    exact ((cg (fun t => t ◇ q14) (apc6 q15 (q15 ◇ q15) (q15 ◇ q15))).symm).trans (((cg (fun t => t ◇ q14) (cg (fun t => q15 ◇ t) (apc8 q15 q14))).symm).trans (apc0 q15 q14 q15))
  exact ((apc9 x z).symm).trans ((apc9 (z ◇ x) (y ◇ (y ◇ (z ◇ z)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35259_to_25336 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_35259_to_25336
