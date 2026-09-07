-- Equation45098 → Equation45197
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (((x ◇ x) ◇ z) ◇ w)
-- Conclusion: x ◇ x = y ◇ (((z ◇ z) ◇ x) ◇ x)
-- Original submission SHA-256: 3fab7bf0fdbfdb92793daaf58f44c5cb039d1941e149f534b66435d08e950da8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (((x ◇ x) ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (((z ◇ z) ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (y ◇ (((z ◇ z) ◇ x) ◇ x)):=(h x x (((z ◇ z) ◇ x) ◇ x) x).trans ((((((h z y x x).symm).trans (h z x (((z ◇ z) ◇ x) ◇ x) x)).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) ((h z (z ◇ z) x x).symm)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) (h z (x ◇ x) x x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45098_to_45197 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45098_to_45197
