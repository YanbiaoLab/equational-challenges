-- Equation5133 → Equation10178
-- Recorded verdict: true
-- Premise: x = y ◇ (y ◇ (z ◇ (x ◇ (z ◇ z))))
-- Conclusion: x = y ◇ ((x ◇ x) ◇ ((y ◇ z) ◇ z))
-- Original submission SHA-256: 01386526205a4d1a8179635b90f69a613d82c6c32071147bcfbfc3254f9da036
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (z ◇ (x ◇ (z ◇ z))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ x) ◇ ((y ◇ z) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) ((h (q0 ◇ q0) (q0 ◇ q0) q0).symm)).symm).trans ((h q0 (q0 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (q1 q2 q3:G), (q3 ◇ (q3 ◇ ((q1 ◇ q1) ◇ (q2 ◇ q1)))) = q2:=by
    intro q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (apc0 q1))))).symm).trans ((h q2 q3 (q1 ◇ q1)).symm)
  have apc2 : forall (q4:G), (q4 ◇ (q4 ◇ q4)) = q4:=by
    intro q4
    exact ((cg (fun t => t ◇ (q4 ◇ q4)) (apc0 q4)).symm).trans (((cg (fun t => ((q4 ◇ q4) ◇ (q4 ◇ q4)) ◇ t) (apc0 (q4 ◇ q4))).symm).trans (apc1 q4 q4 ((q4 ◇ q4) ◇ (q4 ◇ q4))))
  have apc4 : forall (q5 q6:G), (q6 ◇ (q5 ◇ (q6 ◇ q6))) = q5:=by
    intro q5 q6
    exact ((apc2 (q6 ◇ (q5 ◇ (q6 ◇ q6)))).symm).trans ((h q5 (q6 ◇ (q5 ◇ (q6 ◇ q6))) q6).symm)
  have apc5 : forall (x y z:G), (y ◇ (y ◇ x)) = (x ◇ x):=by
    intro x y z
    exact ((cg (fun t => y ◇ t) (cg (fun t => y ◇ t) (apc4 x z))).symm).trans ((((h x y z).symm).trans (h x x x)).trans ((cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (apc2 x)))).trans (cg (fun t => x ◇ t) (apc2 x))))
  have apc6 : forall (q4 q7:G), (q4 ◇ q4) = q4:=by
    intro q4 q7
    exact ((apc5 q4 q7 (q7 ◇ (q7 ◇ q4))).symm).trans (((cg (fun t => q7 ◇ t) (cg (fun t => q7 ◇ t) (apc0 q4))).symm).trans (apc1 q4 q4 q7))
  have apc7 : forall (x y z q4 q7:G), (y ◇ (y ◇ x)) = x:=by
    intro x y z q4 q7
    exact (apc5 x y z).trans (apc6 x (x ◇ x))
  have apc8 : forall (q8 q9:G), (q8 ◇ (q9 ◇ q8)) = q9:=by
    intro q8 q9
    exact (((cg (fun t => t ◇ ((q9 ◇ q8) ◇ (q9 ◇ q8))) (apc6 q8 (q8 ◇ q8))).trans (cg (fun t => q8 ◇ t) (apc6 (q9 ◇ q8) ((q9 ◇ q8) ◇ (q9 ◇ q8))))).symm).trans (((cg (fun t => (q8 ◇ q8) ◇ t) (apc5 (q9 ◇ q8) (q8 ◇ q8) q8)).symm).trans (apc1 q8 q9 (q8 ◇ q8)))
  have apc10 : forall (q10 q11:G), (q11 ◇ q10) = (q10 ◇ q11):=by
    intro q10 q11
    exact ((cg (fun t => q11 ◇ t) (apc8 q11 q10)).symm).trans (apc7 (q10 ◇ q11) q11 q10 q10 q10)
  have apc11 : forall (q12 q13:G), ((q12 ◇ q13) ◇ q13) = q12:=by
    intro q12 q13
    exact ((((cg (fun t => t ◇ q13) (cg (fun t => t ◇ (q13 ◇ q12)) (apc10 q12 q13))).trans (cg (fun t => t ◇ q13) (cg (fun t => (q12 ◇ q13) ◇ t) (apc10 q12 q13)))).trans (cg (fun t => t ◇ q13) (apc6 (q12 ◇ q13) ((q12 ◇ q13) ◇ (q12 ◇ q13))))).symm).trans ((((cg (fun t => ((q13 ◇ q12) ◇ (q13 ◇ q12)) ◇ t) (apc1 q12 q13 ((q13 ◇ q12) ◇ (q13 ◇ q12)))).symm).trans (apc1 (q13 ◇ q12) (q12 ◇ q12) ((q13 ◇ q12) ◇ (q13 ◇ q12)))).trans (apc6 q12 (q12 ◇ q12)))
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((x ◇ x) ◇ ((y ◇ z) ◇ z))):=((((cg (fun t => y ◇ t) (cg (fun t => t ◇ ((y ◇ z) ◇ z)) (apc6 x (x ◇ x)))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (apc11 y z)))).trans (apc10 (x ◇ y) y)).trans (apc11 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5133_to_10178 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5133_to_10178
