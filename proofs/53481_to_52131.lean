-- Equation53481 → Equation52131
-- Recorded verdict: true
-- Premise: x * y = (((z * x) * z) * w) * x
-- Conclusion: x * x = ((y * (x * z)) * y) * z
-- Original submission SHA-256: f206af60f764e43866959b69bec3990ace0ef66582570931e7cd86a83fa1c3c3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ x) ◇ z) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ (x ◇ z)) ◇ y) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ q2) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ q2) ((h q1 q0 q2 (q2 ◇ q1)).symm)).symm).trans ((h q2 q3 (q2 ◇ q1) q1).symm)).trans (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3))
  have apc6 : forall (q4 q0 q3 q5 q6 q1:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = (q3 ◇ q0):=by
    intro q4 q0 q3 q5 q6 q1
    exact (((h q3 q0 q5 q4).trans (h (((q5 ◇ q3) ◇ q5) ◇ q4) q3 q6 q1)).trans ((((((((((cg (fun t => t ◇ (((q5 ◇ q3) ◇ q5) ◇ q4)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q6) (cg (fun t => q6 ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q5) (apc0 q5 q3 (q5 ◇ q3) (q5 ◇ q3)))))))).trans (cg (fun t => t ◇ (((q5 ◇ q3) ◇ q5) ◇ q4)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q6) (cg (fun t => q6 ◇ t) (cg (fun t => t ◇ q4) (apc1 q5 q5 q5 ((q5 ◇ q5) ◇ q5)))))))).trans (cg (fun t => t ◇ (((q5 ◇ q3) ◇ q5) ◇ q4)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q6) (cg (fun t => q6 ◇ t) (apc1 q5 q5 q4 ((q5 ◇ q5) ◇ q4))))))).trans (cg (fun t => (((q6 ◇ (q4 ◇ q4)) ◇ q6) ◇ q1) ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q5) (apc0 q5 q3 (q5 ◇ q3) (q5 ◇ q3)))))).trans (cg (fun t => t ◇ (((q5 ◇ q5) ◇ q5) ◇ q4)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q6) (apc0 q6 (q4 ◇ q4) (q6 ◇ (q4 ◇ q4)) (q6 ◇ (q4 ◇ q4))))))).trans (cg (fun t => (((q6 ◇ q6) ◇ q6) ◇ q1) ◇ t) (cg (fun t => t ◇ q4) (apc1 q5 q5 q5 ((q5 ◇ q5) ◇ q5))))).trans (cg (fun t => t ◇ ((q5 ◇ q5) ◇ q4)) (cg (fun t => t ◇ q1) (apc1 q6 q6 q6 ((q6 ◇ q6) ◇ q6))))).trans (cg (fun t => ((q6 ◇ q6) ◇ q1) ◇ t) (apc1 q5 q5 q4 ((q5 ◇ q5) ◇ q4)))).trans (cg (fun t => t ◇ (q4 ◇ q4)) (apc1 q6 q6 q1 ((q6 ◇ q6) ◇ q1)))).trans (apc1 q1 q1 (q4 ◇ q4) ((q1 ◇ q1) ◇ (q4 ◇ q4))))).symm
  exact ((apc6 (x ◇ x) x x (x ◇ x) (x ◇ x) (x ◇ x)).symm).trans (apc6 (x ◇ x) z ((y ◇ (x ◇ z)) ◇ y) (x ◇ x) (x ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53481_to_52131 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53481_to_52131
