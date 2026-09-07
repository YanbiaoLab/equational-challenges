-- Equation51930 → Equation59088
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * (x * w)) * w
-- Conclusion: (x * x) * x = y * ((x * y) * y)
-- Original submission SHA-256: 8044000aa64f5c52849271729e07e161e95cd1aa178b717feb7939e5c8baa16d
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ (x ◇ w)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ x = y ◇ ((x ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3 q4:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ (q2 ◇ q1)) (apc0 q0 q3 (q0 ◇ q3) (q0 ◇ q3)))).trans (congrArg (fun t => t ◇ q1) (apc0 (q0 ◇ q0) (q2 ◇ q1) ((q0 ◇ q0) ◇ (q2 ◇ q1)) ((q0 ◇ q0) ◇ (q2 ◇ q1))))).symm).trans ((((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q0 q3 q0 q1).symm))).symm).trans ((h q2 q4 ((q0 ◇ q1) ◇ (q0 ◇ q1)) q1).symm)).trans (apc0 q2 q4 (q2 ◇ q4) (q2 ◇ q4)))
  have apc5 : forall (q5 q6 q7:G), (q7 ◇ q7) = (q6 ◇ q5):=by
    intro q5 q6 q7
    exact ((h q6 q5 q6 q6).trans (apc1 q6 q6 q7 q5 q5)).symm
  exact ((apc5 x (x ◇ x) ((x ◇ x) ◇ x)).symm).trans (apc5 ((x ◇ y) ◇ y) y ((x ◇ x) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51930_to_59088 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51930_to_59088
