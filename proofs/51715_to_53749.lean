-- Equation51715 → Equation53749
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (z * x)) * x
-- Conclusion: x * y = (((z * w) * w) * y) * x
-- Original submission SHA-256: 9b522b084bb44e6e6ec985a0b1762c66aea0c6729bb4ebd905b2ede2363e9ee8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ (z ◇ x)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ w) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc4 : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q0 ◇ q1)) (apc0 q0 q1 (q0 ◇ q1)))).trans (cg (fun t => t ◇ q1) (cg (fun t => (q0 ◇ q0) ◇ t) (apc0 q0 q1 (q0 ◇ q1))))).symm).trans (((h q1 q0 q0).symm).trans (apc0 q1 q0 q0))
  have apc6 : forall (q2 q3 q4 q5:G), (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) = (q4 ◇ q2):=by
    intro q2 q3 q4 q5
    exact (((h q4 q2 q3).trans (h ((q3 ◇ q4) ◇ (q3 ◇ q4)) q4 q5)).trans (((((((((cg (fun t => t ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4))) (cg (fun t => t ◇ (q5 ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4)))) (cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (q3 ◇ q4)) (apc0 q3 q4 (q3 ◇ q4)))))).trans (cg (fun t => t ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4))) (cg (fun t => t ◇ (q5 ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4)))) (cg (fun t => q5 ◇ t) (cg (fun t => (q3 ◇ q3) ◇ t) (apc0 q3 q4 (q3 ◇ q4))))))).trans (cg (fun t => t ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4))) (cg (fun t => (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (q3 ◇ q4)) (apc0 q3 q4 (q3 ◇ q4))))))).trans (cg (fun t => t ◇ ((q3 ◇ q4) ◇ (q3 ◇ q4))) (cg (fun t => (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => (q3 ◇ q3) ◇ t) (apc0 q3 q4 (q3 ◇ q4))))))).trans (cg (fun t => ((q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3)))) ◇ t) (cg (fun t => t ◇ (q3 ◇ q4)) (apc0 q3 q4 (q3 ◇ q4))))).trans (cg (fun t => ((q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3)))) ◇ t) (cg (fun t => (q3 ◇ q3) ◇ t) (apc0 q3 q4 (q3 ◇ q4))))).trans (cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (cg (fun t => t ◇ (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3)))) (apc0 q5 ((q3 ◇ q3) ◇ (q3 ◇ q3)) (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))))))).trans (cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (cg (fun t => (q5 ◇ q5) ◇ t) (apc0 q5 ((q3 ◇ q3) ◇ (q3 ◇ q3)) (q5 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))))))).trans (apc4 q5 ((q3 ◇ q3) ◇ (q3 ◇ q3))))).symm
  exact ((apc6 y (x ◇ y) x (x ◇ y)).symm).trans (apc6 x (x ◇ y) (((z ◇ w) ◇ w) ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51715_to_53749 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51715_to_53749
