-- Equation3501 → Equation43370
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ ((z ◇ z) ◇ z)
-- Conclusion: x ◇ x = y ◇ ((x ◇ z) ◇ (w ◇ w))
-- Original submission SHA-256: 6cfa7425cf4fafa2ef50aca798a59035772642805424d02a5b58fd81ae5bc0b9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((z ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ ((x ◇ z) ◇ (w ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ x) = (y ◇ ((x ◇ z) ◇ (w ◇ w))):=((((h x y (w ◇ w)).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ (w ◇ w)) (h (w ◇ w) x w)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ (w ◇ w)) ((h w x w).symm)))).trans (congrArg (fun t => y ◇ t) (h (w ◇ w) (x ◇ z) ((z ◇ z) ◇ z)))).trans (((congrArg (fun t => y ◇ t) (congrArg (fun t => (x ◇ z) ◇ t) (h w (w ◇ w) z))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (x ◇ z) ◇ t) (congrArg (fun t => t ◇ ((z ◇ z) ◇ z)) (h w ((z ◇ z) ◇ z) z))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3501_to_43370 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3501_to_43370
