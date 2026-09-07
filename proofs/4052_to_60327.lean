-- Equation4052 → Equation60327
-- Recorded verdict: true
-- Premise: x * y = (z * (w * z)) * w
-- Conclusion: (x * y) * y = (x * z) * (y * w)
-- Original submission SHA-256: fb62a268615d1d2a182ce8848587a9264ea2e5c3b04cfedc42e69696999fee94
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ z)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = (x ◇ z) ◇ (y ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    ((x ◇ y) ◇ y) = ((x ◇ z) ◇ (y ◇ w)):=(h (x ◇ y) y ((x ◇ y) ◇ y) ((x ◇ z) ◇ (y ◇ w))).trans ((h (x ◇ z) (y ◇ w) ((x ◇ y) ◇ y) ((x ◇ z) ◇ (y ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4052_to_60327 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4052_to_60327
