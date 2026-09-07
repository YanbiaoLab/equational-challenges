-- Equation48315 → Equation4015
-- Recorded verdict: true
-- Premise: x * y = (z * (y * w)) * (z * u)
-- Conclusion: x * y = (z * (y * z)) * z
-- Original submission SHA-256: da02c00fd42bb57d132f1d47057da777421a668c027e74c1fac8d0cf766bf68e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (y ◇ w)) ◇ (z ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ (q0 ◇ q2)) ◇ (q4 ◇ q1)) = (q3 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ q1)) (congrArg (fun t => q4 ◇ t) (apc0 q0 q2 q0 q0 q0))).symm).trans ((h q3 q2 q4 q2 q1).symm)
  have apc5 : forall (x y z w u:G), ((z ◇ (y ◇ w)) ◇ (z ◇ u)) = ((x ◇ (y ◇ x)) ◇ (x ◇ x)):=by
    intro x y z w u
    exact ((h x y z w u).symm).trans (h x y x x x)
  have apc7 : forall (q5 q6 q7 q8:G), ((q5 ◇ (q6 ◇ q5)) ◇ (q5 ◇ q5)) = (q8 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc5 q5 q6 q5 q7 q5).symm).trans (apc1 q6 q5 q7 q8 q5)
  exact ((apc7 (x ◇ y) ((z ◇ (y ◇ z)) ◇ z) y x).symm).trans (apc7 (x ◇ y) ((z ◇ (y ◇ z)) ◇ z) z (z ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48315_to_4015 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48315_to_4015
