-- Equation45574 → Equation57892
-- Recorded verdict: true
-- Premise: x * y = z * (((x * y) * w) * w)
-- Conclusion: x * (y * z) = ((x * w) * u) * y
-- Original submission SHA-256: 1a5a30b28e445d5f17e0bb8d4777b1ff21de0b95b98e0d665c1797081234a168
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((x ◇ y) ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = ((x ◇ w) ◇ u) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) ((h q0 q1 ((q2 ◇ q3) ◇ (((q0 ◇ q1) ◇ q0) ◇ q0)) q0).symm)).symm).trans ((h q2 q3 q4 (((q0 ◇ q1) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q0 q1 q2 q3 q4:G), (q2 ◇ q3) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).symm).trans (apc0 q0 q1 q0 q0 q4)
  exact (apc1 (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) x (y ◇ z) (x ◇ (y ◇ z))).trans ((apc1 (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) ((x ◇ w) ◇ u) y (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45574_to_57892 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45574_to_57892
