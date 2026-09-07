-- Equation51378 → Equation53030
-- Recorded verdict: true
-- Premise: x ◇ x = ((y ◇ z) ◇ (w ◇ u)) ◇ v
-- Conclusion: x ◇ x = (((y ◇ y) ◇ y) ◇ x) ◇ y
-- Original submission SHA-256: dc34434f7cd576a39ba28a93e438e28d322693323241080cdb84e218e7774cda
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ x = ((y ◇ z) ◇ (w ◇ u)) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (((y ◇ y) ◇ y) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y
  have sameSquare : ∀ (a b : G), a ◇ a = b ◇ b := by
    intro a b
    exact (h a a a a a a).trans ((h b a a a a a).symm)
  have squareAbsorb : ∀ (a t : G), (a ◇ a) ◇ t = a ◇ a := by
    intro a t
    have expand : a ◇ a = ((a ◇ a) ◇ (a ◇ a)) ◇ t := h a a a a a t
    have collapse : (a ◇ a) ◇ (a ◇ a) = a ◇ a := sameSquare (a ◇ a) a
    exact (expand.trans (congrArg (fun q => q ◇ t) collapse)).symm
  have step1 : (y ◇ y) ◇ y = y ◇ y := squareAbsorb y y
  have step2 : ((y ◇ y) ◇ y) ◇ x = y ◇ y :=
    (congrArg (fun q => q ◇ x) step1).trans (squareAbsorb y x)
  have step3 : (((y ◇ y) ◇ y) ◇ x) ◇ y = y ◇ y :=
    (congrArg (fun q => q ◇ y) step2).trans (squareAbsorb y y)
  exact (sameSquare x y).trans step3.symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51378_to_53030 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51378_to_53030
