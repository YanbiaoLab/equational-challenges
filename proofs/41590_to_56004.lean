-- Equation41590 → Equation56004
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (x ◇ (z ◇ w)))
-- Conclusion: x ◇ (y ◇ y) = (z ◇ x) ◇ (w ◇ w)
-- Original submission SHA-256: 275a23f93c86607dbd1b63a309fb97c2b3043b1faa6ae6a8facb2a226476ed13
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ x) ◇ (w ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ (y ◇ y)) = ((z ◇ x) ◇ (w ◇ w)):=(((((congrArg (fun t => x ◇ t) (h y w y (w ◇ w))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => w ◇ t) ((h y y w w).symm)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => w ◇ t) (h y w w w)))).trans ((h w x y (y ◇ (w ◇ w))).symm)).trans (h w (z ◇ x) w (w ◇ w))).trans ((congrArg (fun t => (z ◇ x) ◇ t) (h w w w w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41590_to_56004 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41590_to_56004
