-- Equation35117 → Equation21913
-- Recorded verdict: true
-- Premise: x = ((y * z) * ((y * y) * y)) * y
-- Conclusion: x = (y * (z * x)) * (z * (w * u))
-- Original submission SHA-256: d159dbf063bdaa7c29928586a42e59aefbdff9a45b39e9b6018e264ed1aac406
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ ((y ◇ y) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ x)) ◇ (z ◇ (w ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  calc
    x = ((y ◇ (z ◇ x)) ◇ (z ◇ (w ◇ u))):=(h x x ((y ◇ (z ◇ x)) ◇ (z ◇ (w ◇ u)))).trans ((h ((y ◇ (z ◇ x)) ◇ (z ◇ (w ◇ u))) x ((y ◇ (z ◇ x)) ◇ (z ◇ (w ◇ u)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35117_to_21913 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_35117_to_21913
