-- Equation534 → Equation36363
-- Recorded verdict: true
-- Premise: x = y * (y * (z * (w * z)))
-- Conclusion: x = (((x * y) * y) * (x * z)) * y
-- Original submission SHA-256: e9fc2f11f784024430ad5af5d9b1322eda13b316c69d66c99b6e1eb3767005b4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (y ◇ (z ◇ (w ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ y) ◇ (x ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    x = ((((x ◇ y) ◇ y) ◇ (x ◇ z)) ◇ y):=(h x x x ((((x ◇ y) ◇ y) ◇ (x ◇ z)) ◇ y)).trans ((h ((((x ◇ y) ◇ y) ◇ (x ◇ z)) ◇ y) x x ((((x ◇ y) ◇ y) ◇ (x ◇ z)) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_534_to_36363 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_534_to_36363
