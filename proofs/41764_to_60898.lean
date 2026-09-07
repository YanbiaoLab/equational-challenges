-- Equation41764 → Equation60898
-- Recorded verdict: true
-- Premise: x * y = x * (x * (z * (w * x)))
-- Conclusion: (x * x) * y = (x * (z * x)) * w
-- Original submission SHA-256: 359d7e730852f5fd1416f7629d69fb581e468cbcd6114021fe84976f3d7ff97a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (x ◇ (z ◇ (w ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (x ◇ (z ◇ x)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1 q2 q3 q4
    exact (((((((congrArg (fun t => (q0 ◇ (q2 ◇ q3)) ◇ t) (congrArg (fun t => t ◇ (q3 ◇ q4)) (congrArg (fun t => q0 ◇ t) (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3))))).trans (congrArg (fun t => t ◇ ((q0 ◇ (q2 ◇ q2)) ◇ (q3 ◇ q4))) (congrArg (fun t => q0 ◇ t) (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3))))).trans (congrArg (fun t => (q0 ◇ (q2 ◇ q2)) ◇ t) (congrArg (fun t => t ◇ (q3 ◇ q4)) (apc0 q0 (q2 ◇ q2) (q0 ◇ (q2 ◇ q2)) (q0 ◇ (q2 ◇ q2)))))).trans (congrArg (fun t => t ◇ ((q0 ◇ q0) ◇ (q3 ◇ q4))) (apc0 q0 (q2 ◇ q2) (q0 ◇ (q2 ◇ q2)) (q0 ◇ (q2 ◇ q2))))).trans (congrArg (fun t => (q0 ◇ q0) ◇ t) (apc0 (q0 ◇ q0) (q3 ◇ q4) ((q0 ◇ q0) ◇ (q3 ◇ q4)) ((q0 ◇ q0) ◇ (q3 ◇ q4))))).trans (apc0 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans ((((congrArg (fun t => (q0 ◇ (q2 ◇ q3)) ◇ t) (congrArg (fun t => (q0 ◇ (q2 ◇ q3)) ◇ t) ((h q3 q4 q0 q2).symm))).symm).trans ((h (q0 ◇ (q2 ◇ q3)) q1 q3 q3).symm)).trans ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q0 ◇ t) (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3)))).trans (congrArg (fun t => t ◇ q1) (apc0 q0 (q2 ◇ q2) (q0 ◇ (q2 ◇ q2)) (q0 ◇ (q2 ◇ q2))))))
  have apc2 : forall (q2 q4 q0 q3 q1:G), ((q0 ◇ q0) ◇ q1) = ((q0 ◇ q0) ◇ q0):=by
    intro q2 q4 q0 q3 q1
    exact ((apc1 q0 q1 q2 q3 q4).symm).trans (apc1 q0 q0 q2 q3 q4)
  exact (calc
    ((x ◇ x) ◇ y) = ((x ◇ x) ◇ x):=apc2 w w x w y
    _ = ((x ◇ x) ◇ w):=(apc2 w w x w w).symm
    _ = ((x ◇ (z ◇ x)) ◇ w):=(congrArg (fun t => t ◇ w) (apc0 x (z ◇ x) w w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41764_to_60898 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41764_to_60898
