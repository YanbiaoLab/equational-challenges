-- Equation46879 → Equation47869
-- Recorded verdict: true
-- Premise: x * x = (y * x) * ((z * w) * u)
-- Conclusion: x * x = (y * (z * w)) * (u * u)
-- Original submission SHA-256: 9786c0ffe82f3634244b6e0738e5f68b241c9892ba75c4dda8dcdb0eb03ddd5b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (y ◇ x) ◇ ((z ◇ w) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (y ◇ (z ◇ w)) ◇ (u ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have l0 : forall (x u : G), (x ◇ x) = (u ◇ u) := by
    intro x u
    have apc0 : forall (q0 q1 q2 : G), ((q2 ◇ q1) ◇ (q0 ◇ q0)) = (q1 ◇ q1) := by
      intro q0 q1 q2
      exact ((rfl).symm).trans ((((congrArg (fun t => (q2 ◇ q1) ◇ t) ((h q0 q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0 ((q0 ◇ q0) ◇ q0)).symm)).trans (rfl))
    have apc2 : forall (q3 q4 q5 : G), (q4 ◇ q4) = (q3 ◇ q3) := by
      intro q3 q4 q5
      exact ((apc0 q5 q4 q4).symm).trans ((((congrArg (fun t => t ◇ (q5 ◇ q5)) (apc0 q3 q4 q3)).symm).trans (apc0 q5 (q3 ◇ q3) (q3 ◇ q4))).trans (apc0 q3 q3 q3))
    exact (apc2 (x ◇ x) x (x ◇ x)).trans ((apc2 (x ◇ x) u (x ◇ x)).symm)
  have l3 : forall (x w u : G), (u ◇ u) = ((x ◇ w) ◇ (u ◇ u)) := by
    intro x w u
    exact (calc
      (u ◇ u) = (w ◇ w) := (l0 w u).symm
      _ = ((x ◇ w) ◇ ((u ◇ u) ◇ (u ◇ u))) := h w x u u (u ◇ u)
      _ = ((x ◇ w) ◇ (u ◇ u)) := congrArg (fun t => (x ◇ w) ◇ t) (l0 (u ◇ u) u))
  have reduced_goal : (x ◇ x) = (u ◇ u) := by
    have l0 : forall (x u : G), (x ◇ x) = (u ◇ u) := by
      intro x u
      have apc0 : forall (q0 q1 q2 : G), ((q2 ◇ q1) ◇ (q0 ◇ q0)) = (q1 ◇ q1) := by
        intro q0 q1 q2
        exact ((rfl).symm).trans ((((congrArg (fun t => (q2 ◇ q1) ◇ t) ((h q0 q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0 ((q0 ◇ q0) ◇ q0)).symm)).trans (rfl))
      have apc2 : forall (q3 q4 q5 : G), (q4 ◇ q4) = (q3 ◇ q3) := by
        intro q3 q4 q5
        exact ((apc0 q5 q4 q4).symm).trans ((((congrArg (fun t => t ◇ (q5 ◇ q5)) (apc0 q3 q4 q3)).symm).trans (apc0 q5 (q3 ◇ q3) (q3 ◇ q4))).trans (apc0 q3 q3 q3))
      exact (apc2 (x ◇ x) x (x ◇ x)).trans ((apc2 (x ◇ x) u (x ◇ x)).symm)
    exact (l0 x (x ◇ x)).trans ((l0 u (x ◇ x)).symm)
  exact (calc
    (x ◇ x) = (x ◇ x) := rfl
    _ = (u ◇ u) := reduced_goal
    _ = ((y ◇ (z ◇ w)) ◇ (u ◇ u)) := ((l3 y (z ◇ w) u).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46879_to_47869 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46879_to_47869
