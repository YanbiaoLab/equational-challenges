-- Equation45892 → Equation57184
-- Recorded verdict: true
-- Premise: x * y = z * (((w * u) * z) * w)
-- Conclusion: x * (y * z) = (w * (x * z)) * x
-- Original submission SHA-256: 7898e0a57c02eafd84ca01c5a490829ed8f395152c8eb6c9023e52c716f615bc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (((w ◇ u) ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (w ◇ (x ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (z ◇ z) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h z z z w u).symm)).symm
  exact ((apc0 x (y ◇ z) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).symm).trans (apc0 (w ◇ (x ◇ z)) x (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45892_to_57184 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45892_to_57184
