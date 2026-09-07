-- Equation42494 → Equation42520
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ w) ◇ u))
-- Conclusion: x ◇ x = y ◇ (y ◇ ((z ◇ y) ◇ y))
-- Original submission SHA-256: 998774422bb60555921077b96f3cc06a8cc1872eeab0025b236e407d221c82f7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ (x ◇ ((z ◇ w) ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ ((z ◇ y) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (y ◇ (y ◇ ((z ◇ y) ◇ y))):=(h x x x x ((z ◇ y) ◇ y)).trans ((((((h y y z y y).symm).trans (h y x x x ((z ◇ y) ◇ y))).trans (congrArg (fun t => x ◇ t) ((h (x ◇ x) y z y y).symm))).trans (congrArg (fun t => x ◇ t) (h (x ◇ x) x z y y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42494_to_42520 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42494_to_42520
