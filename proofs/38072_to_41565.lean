-- Equation38072 → Equation41565
-- Recorded verdict: true
-- Premise: x = ((x * ((x * y) * z)) * w) * u
-- Conclusion: x * x = x * (y * (z * (x * y)))
-- Original submission SHA-256: e3f3664f0cd14582fef4eb465302b3908d50e99dc7fa3e3c1469acab81339e42
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((x ◇ ((x ◇ y) ◇ z)) ◇ w) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (y ◇ (z ◇ (x ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q0 ◇ q1) ◇ q2)) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 q2 (((q0 ◇ ((q0 ◇ q1) ◇ q2)) ◇ q0) ◇ q0) q0).symm)).symm).trans ((h (q0 ◇ ((q0 ◇ q1) ◇ q2)) q0 q0 q0 q3).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q0 ◇ q3) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q1 q2 q0)
  exact (apc1 x (x ◇ x) (x ◇ x) x).trans ((apc1 x (x ◇ x) (x ◇ x) (y ◇ (z ◇ (x ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38072_to_41565 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38072_to_41565
