-- Equation54825 → Equation54798
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = z ◇ ((x ◇ w) ◇ w)
-- Conclusion: x ◇ (x ◇ y) = y ◇ ((z ◇ y) ◇ y)
-- Original submission SHA-256: 4c982a6ede3a6723f4946f6cfe23cede3fb8ef61921d5d17ade8e97d1306e67d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ ((x ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = y ◇ ((z ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ (x ◇ y)) = (y ◇ ((z ◇ y) ◇ y)):=((h x y y y).trans ((h x ((z ◇ y) ◇ y) y y).symm)).trans ((((((h z y y y).symm).trans (h z y x ((z ◇ y) ◇ y))).trans (congrArg (fun t => x ◇ t) ((h z x (z ◇ ((z ◇ y) ◇ y)) y).symm))).trans (congrArg (fun t => x ◇ t) (h z x x y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54825_to_54798 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54825_to_54798
