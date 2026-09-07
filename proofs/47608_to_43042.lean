-- Equation47608 → Equation43042
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((w * x) * w)
-- Conclusion: x * y = z * (y * ((w * x) * w))
-- Original submission SHA-256: faac4896063b02befbd9deb13e6a8720ab96375ad0f809ad48f101f0357127d4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ ((w ◇ x) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (y ◇ ((w ◇ x) ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w : G), (x ◇ y) = (x ◇ x) := by
    intro x y z w
    exact ((rfl).symm).trans (((h x y z w).trans ((h x x z w).symm)).trans (rfl))
  have apc1 : forall (q0 q1 q2 q3 : G), ((q3 ◇ q0) ◇ (q3 ◇ q0)) = (q1 ◇ q1) := by
    intro q0 q1 q2 q3
    exact ((rfl).symm).trans ((((apc0 (q3 ◇ q0) ((q0 ◇ q1) ◇ q0) q0 q0).symm).trans ((h q1 q2 q3 q0).symm)).trans (apc0 q1 q2 (q1 ◇ q2) (q1 ◇ q2)))
  have apc2 : forall (q4 q5 q6 : G), (q5 ◇ q5) = (q4 ◇ q4) := by
    intro q4 q5 q6
    exact (((rfl).symm).trans ((((apc1 q4 q4 q4 (q4 ◇ q5)).symm).trans ((h q5 q6 (q4 ◇ q5) q4).symm)).trans (apc0 q5 q6 (q5 ◇ q6) (q5 ◇ q6)))).symm
  exact (calc
    (x ◇ y) = (x ◇ x) := apc0 x y w w
    _ = (z ◇ z) := apc2 z x w
    _ = (z ◇ (y ◇ ((w ◇ x) ◇ w))) := (apc0 z (y ◇ ((w ◇ x) ◇ w)) w w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47608_to_43042 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47608_to_43042
