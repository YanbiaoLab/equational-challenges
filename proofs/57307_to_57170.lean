-- Equation57307 → Equation57170
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (w ◇ (u ◇ u)) ◇ v
-- Conclusion: x ◇ (y ◇ z) = (z ◇ (w ◇ u)) ◇ z
-- Original submission SHA-256: 319a5782928c2dae16251ab1d12899a7a8a495be0a9bc7665c3c713d8caab2f6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = (w ◇ (u ◇ u)) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (z ◇ (w ◇ u)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  calc
    (x ◇ (y ◇ z)) = ((z ◇ (w ◇ u)) ◇ z):=((h x y z u w z).trans (congrArg (fun t => t ◇ z) (h u w w u u (w ◇ u)))).trans ((congrArg (fun t => t ◇ z) (h z w u u u (w ◇ u))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_57307_to_57170 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_57307_to_57170
