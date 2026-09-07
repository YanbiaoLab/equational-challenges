-- Equation51263 → Equation60112
-- Recorded verdict: true
-- Premise: x * x = ((y * x) * (z * w)) * w
-- Conclusion: (x * x) * y = (z * z) * (y * z)
-- Original submission SHA-256: 8659e7523e5fc23289676065df646868dfaab75b4967099bc79f38916d28d837
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = ((y ◇ x) ◇ (z ◇ w)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (z ◇ z) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have l0 : forall (x y z : G), ((x ◇ x) ◇ y) = ((z ◇ z) ◇ y) := by
    intro x y z
    have apc0 : forall (q0 q1 q2 q3 : G), ((q1 ◇ (q3 ◇ q2)) ◇ (q1 ◇ (q3 ◇ q2))) = ((q0 ◇ q0) ◇ q2) := by
      intro q0 q1 q2 q3
      exact (((rfl).symm).trans ((((congrArg (fun t => t ◇ q2) ((h q0 q0 q1 (q3 ◇ q2)).symm)).symm).trans ((h (q1 ◇ (q3 ◇ q2)) (q0 ◇ q0) q3 q2).symm)).trans (rfl))).symm
    exact ((apc0 x ((x ◇ x) ◇ y) y ((z ◇ z) ◇ y)).symm).trans (((apc0 z ((x ◇ x) ◇ y) y ((z ◇ z) ◇ y)).symm).symm)
  have l1 : forall (x w : G), (w ◇ w) = ((x ◇ x) ◇ w) := by
    intro x w
    exact (calc
      (w ◇ w) = (w ◇ w) := (rfl).symm
      _ = (((w ◇ w) ◇ (w ◇ w)) ◇ w) := h w w w w
      _ = ((x ◇ x) ◇ w) := (l0 x w (w ◇ w)).symm)
  have l3 : forall (x y : G), (y ◇ y) = ((x ◇ x) ◇ x) := by
    intro x y
    exact (calc
      (y ◇ y) = (y ◇ y) := (rfl).symm
      _ = (((y ◇ y) ◇ (x ◇ x)) ◇ x) := h y y x x
      _ = ((x ◇ x) ◇ x) := (congrArg (fun t => t ◇ x) ((l0 x (x ◇ x) y).symm)).trans ((l0 x x (x ◇ x)).symm))
  have reduced_goal : (y ◇ y) = ((y ◇ z) ◇ (y ◇ z)) := by
    have l0 : forall (x y z : G), ((x ◇ x) ◇ y) = ((z ◇ z) ◇ y) := by
      intro x y z
      have apc0 : forall (q0 q1 q2 q3 : G), ((q1 ◇ (q3 ◇ q2)) ◇ (q1 ◇ (q3 ◇ q2))) = ((q0 ◇ q0) ◇ q2) := by
        intro q0 q1 q2 q3
        exact (((rfl).symm).trans ((((congrArg (fun t => t ◇ q2) ((h q0 q0 q1 (q3 ◇ q2)).symm)).symm).trans ((h (q1 ◇ (q3 ◇ q2)) (q0 ◇ q0) q3 q2).symm)).trans (rfl))).symm
      exact ((apc0 x ((x ◇ x) ◇ y) y ((z ◇ z) ◇ y)).symm).trans (((apc0 z ((x ◇ x) ◇ y) y ((z ◇ z) ◇ y)).symm).symm)
    have l3 : forall (x y : G), (y ◇ y) = ((x ◇ x) ◇ x) := by
      intro x y
      exact (calc
        (y ◇ y) = (y ◇ y) := (rfl).symm
        _ = (((y ◇ y) ◇ (x ◇ x)) ◇ x) := h y y x x
        _ = ((x ◇ x) ◇ x) := (congrArg (fun t => t ◇ x) ((l0 x (x ◇ x) y).symm)).trans ((l0 x x (x ◇ x)).symm))
    exact (l3 (y ◇ y) y).trans ((l3 (y ◇ y) (y ◇ z)).symm)
  exact (calc
    ((x ◇ x) ◇ y) = (y ◇ y) := (l1 x y).symm
    _ = ((y ◇ z) ◇ (y ◇ z)) := reduced_goal
    _ = ((z ◇ z) ◇ (y ◇ z)) := ((l1 z (y ◇ z)).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51263_to_60112 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51263_to_60112
