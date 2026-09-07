-- Equation41590 → Equation3303
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
-- Conclusion: x ◇ x = y ◇ (z ◇ (w ◇ w))
-- Original submission SHA-256: 4697f63d1a0258e62f71b0b4a7dfdf6aff05053b472ded1e6bf12b51e73f402b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ (w ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ x) = (y ◇ (z ◇ (w ◇ w))):=((((((((h x y x (w ◇ w)).trans (congrArg (fun t => y ◇ t) ((h x x w w).symm))).trans (congrArg (fun t => y ◇ t) (h x z x (w ◇ w)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) ((h x x w w).symm)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (h x w x (w ◇ w))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => w ◇ t) ((h x x w w).symm))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => w ◇ t) (h x w w w))))).trans (congrArg (fun t => y ◇ t) ((h w z x (x ◇ (w ◇ w))).symm))).trans (((congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (h w w w w))).trans (congrArg (fun t => y ◇ t) ((h w z w (w ◇ w)).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41590_to_3303 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41590_to_3303
