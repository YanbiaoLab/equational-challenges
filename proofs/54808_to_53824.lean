-- Equation54808 → Equation53824
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = y ◇ ((z ◇ w) ◇ w)
-- Conclusion: x ◇ (x ◇ x) = y ◇ (x ◇ (x ◇ z))
-- Original submission SHA-256: 26e40a1e5375643222e042ccbdede4f7de713e2db7bfd9fac60b2799a3d164bf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = y ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ x) = y ◇ (x ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ (x ◇ x)) = (y ◇ (x ◇ (x ◇ z))):=(((((((((h x x x (x ◇ z)).trans ((h (x ◇ x) x x (x ◇ z)).symm)).trans ((h x (x ◇ x) x x).symm)).trans (congrArg (fun t => x ◇ t) (h x x x z))).trans (h x ((x ◇ z) ◇ z) x (x ◇ z))).trans ((h z ((x ◇ z) ◇ z) x (x ◇ z)).symm)).trans (congrArg (fun t => z ◇ t) ((h z z x z).symm))).trans (h z (z ◇ z) z z)).trans (h (z ◇ z) z x (x ◇ z))).trans (((((congrArg (fun t => y ◇ t) (h x z x x)).trans (congrArg (fun t => y ◇ t) ((h y z x x).symm))).trans (h y (y ◇ z) y z)).trans (h (y ◇ z) z x (x ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54808_to_53824 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54808_to_53824
