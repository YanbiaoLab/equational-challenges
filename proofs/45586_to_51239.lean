-- Equation45586 → Equation51239
-- Recorded verdict: true
-- Premise: x * y = z * (((x * z) * z) * z)
-- Conclusion: x * x = ((y * x) * (y * x)) * y
-- Original submission SHA-256: c174cf8184db546f69e19d3c76ffedd260634c7d5bf3ff5344b4a7c352df3d36
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (((x ◇ z) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((y ◇ x) ◇ (y ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc2 : forall (q0 q1 q2 q3:G), ((((q0 ◇ q0) ◇ q1) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((((((((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) (cg (fun t => (q0 ◇ q2) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (apc0 q0 q1 (q0 ◇ q1))))))).trans (cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (apc0 q0 q1 (q0 ◇ q1))))))).trans (cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) (apc0 q0 q2 (q0 ◇ q2)))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (apc0 q0 q1 (q0 ◇ q1)))))).trans (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) (apc0 (q0 ◇ q0) (((q0 ◇ q0) ◇ q1) ◇ q1) ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)))))).trans (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q1) ◇ t) (apc0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) (((q0 ◇ q0) ◇ q1) ◇ q1) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))))).trans (apc0 (((q0 ◇ q0) ◇ q1) ◇ q1) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((((q0 ◇ q0) ◇ q1) ◇ q1) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm).trans ((((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) ((h q0 q2 q1).symm)))).symm).trans ((h q1 q3 (((q0 ◇ q1) ◇ q1) ◇ q1)).symm)).trans (apc0 q1 q3 (q1 ◇ q3)))
  have apc3 : forall (q4 q5 q6:G), ((((q4 ◇ q4) ◇ q5) ◇ q5) ◇ q6) = (q5 ◇ q5):=by
    intro q4 q5 q6
    exact ((((((cg (fun t => (((q4 ◇ q4) ◇ q5) ◇ q5) ◇ t) (cg (fun t => t ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)) (apc0 (q5 ◇ q5) (((q4 ◇ q4) ◇ q5) ◇ q5) ((q5 ◇ q5) ◇ (((q4 ◇ q4) ◇ q5) ◇ q5))))).trans (cg (fun t => (((q4 ◇ q4) ◇ q5) ◇ q5) ◇ t) (apc0 ((q5 ◇ q5) ◇ (q5 ◇ q5)) (((q4 ◇ q4) ◇ q5) ◇ q5) (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ (((q4 ◇ q4) ◇ q5) ◇ q5))))).trans (apc0 (((q4 ◇ q4) ◇ q5) ◇ q5) (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5))) ((((q4 ◇ q4) ◇ q5) ◇ q5) ◇ (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5)))))).trans (apc2 q4 q5 ((((q4 ◇ q4) ◇ q5) ◇ q5) ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)) ((((q4 ◇ q4) ◇ q5) ◇ q5) ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)))).symm).trans (((cg (fun t => (((q4 ◇ q4) ◇ q5) ◇ q5) ◇ t) (cg (fun t => t ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)) (cg (fun t => t ◇ (((q4 ◇ q4) ◇ q5) ◇ q5)) (apc2 q4 q5 q4 q4)))).symm).trans ((h (((q4 ◇ q4) ◇ q5) ◇ q5) q6 (((q4 ◇ q4) ◇ q5) ◇ q5)).symm))).symm
  have apc5 : forall (q7 q8 q9:G), ((q7 ◇ q7) ◇ q8) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (((apc0 q9 (q9 ◇ q9) (q9 ◇ (q9 ◇ q9))).symm).trans (((cg (fun t => q9 ◇ t) (apc3 q7 q9 q9)).symm).trans ((h (q7 ◇ q7) q8 q9).symm))).symm
  exact ((apc5 x (x ◇ x) x).symm).trans ((apc5 (y ◇ x) y (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45586_to_51239 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45586_to_51239
