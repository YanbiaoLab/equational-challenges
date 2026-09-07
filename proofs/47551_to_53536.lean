-- Equation47551 → Equation53536
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((x * u) * u)
-- Conclusion: x * y = (((z * y) * y) * y) * w
-- Original submission SHA-256: d88d8dad04f01bce6c5e874e4e178853db69e00afd6437fe20919d2c3e74d55f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ ((x ◇ u) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ y) ◇ y) ◇ y) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u : G), (x ◇ y) = (x ◇ x) := by
    intro x y z w u
    exact ((rfl).symm).trans (((h x y z w u).trans ((h x x z w u).symm)).trans (rfl))
  have apc5 : forall (q0 q1 q2 q3 q4 q5 q6 q7 : G), ((q7 ◇ q5) ◇ (q7 ◇ q5)) = ((q4 ◇ q1) ◇ q6) := by
    intro q0 q1 q2 q3 q4 q5 q6 q7
    exact ((((congrArg (fun t => (q7 ◇ q5) ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q0) ◇ q0)) (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3) (q2 ◇ q3)))).trans (congrArg (fun t => (q7 ◇ q5) ◇ t) (apc0 (q2 ◇ q2) ((q2 ◇ q0) ◇ q0) ((q2 ◇ q2) ◇ ((q2 ◇ q0) ◇ q0)) ((q2 ◇ q2) ◇ ((q2 ◇ q0) ◇ q0)) ((q2 ◇ q2) ◇ ((q2 ◇ q0) ◇ q0))))).trans (apc0 (q7 ◇ q5) ((q2 ◇ q2) ◇ (q2 ◇ q2)) ((q7 ◇ q5) ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) ((q7 ◇ q5) ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) ((q7 ◇ q5) ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))))).symm).trans ((((congrArg (fun t => (q7 ◇ q5) ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q0) ◇ q0)) ((h q2 q3 q4 q1 q0).symm))).symm).trans ((h (q4 ◇ q1) q6 q7 q5 ((q2 ◇ q0) ◇ q0)).symm)).trans (rfl))
  have apc6 : forall (q8 q9 q10 q11 q12 : G), ((q9 ◇ q8) ◇ q10) = (q11 ◇ q11) := by
    intro q8 q9 q10 q11 q12
    exact ((rfl).symm).trans ((((apc5 q8 q8 q8 q8 q9 q8 q10 (q11 ◇ q8)).symm).trans ((h q11 q12 (q11 ◇ q8) q8 q8).symm)).trans (apc0 q11 q12 (q11 ◇ q12) (q11 ◇ q12) (q11 ◇ q12)))
  exact (calc
    (x ◇ y) = (x ◇ x) := apc0 x y w w w
    _ = ((((z ◇ y) ◇ y) ◇ y) ◇ w) := (apc6 y ((z ◇ y) ◇ y) w x w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47551_to_53536 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47551_to_53536
