-- Equation50272 → Equation49417
-- Recorded verdict: true
-- Premise: x * y = (z * (w * (u * y))) * u
-- Conclusion: x * y = ((z * w) * u) * (v * z)
-- Original submission SHA-256: 99ecbc0c98622f0a3ecdc30aaa1aad70d36ec15c60707f96359fd19653ce28b9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (w ◇ (u ◇ y))) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ u) ◇ (v ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc1 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc3 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((apc1 (q0 ◇ (q0 ◇ (q0 ◇ q2))) q0 q0 q0 q0).trans ((h q1 q2 q0 q0 q0).symm)).symm
  exact (apc3 (x ◇ y) x y).trans ((apc3 (x ◇ y) ((z ◇ w) ◇ u) (v ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50272_to_49417 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50272_to_49417
