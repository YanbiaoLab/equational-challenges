-- Equation59678 → Equation61351
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = y ◇ ((y ◇ z) ◇ z)
-- Conclusion: (x ◇ y) ◇ z = (x ◇ (y ◇ y)) ◇ z
-- Original submission SHA-256: da888e8496e51b2ca629bb76d1b37ec190e13db9c4c5b90f43aa806a87fae2e8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = y ◇ ((y ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (x ◇ (y ◇ y)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    ((x ◇ y) ◇ z) = ((x ◇ (y ◇ y)) ◇ z):=((((((h x y z).trans ((h (x ◇ y) y z).symm)).trans (congrArg (fun t => t ◇ z) (h x y y))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => y ◇ t) (h y y y)))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => y ◇ t) ((h x y y).symm)))).trans (h y ((x ◇ y) ◇ y) z)).trans ((((((((((h x (y ◇ y) z).trans (congrArg (fun t => (y ◇ y) ◇ t) (h (y ◇ y) z z))).trans (congrArg (fun t => (y ◇ y) ◇ t) ((h x z z).symm))).trans (h y y ((x ◇ z) ◇ z))).trans ((h (x ◇ y) y ((x ◇ z) ◇ z)).symm)).trans (congrArg (fun t => ((x ◇ y) ◇ y) ◇ t) (h x z z))).trans (congrArg (fun t => ((x ◇ y) ◇ y) ◇ t) ((h (x ◇ y) z z).symm))).trans (congrArg (fun t => ((x ◇ y) ◇ y) ◇ t) (congrArg (fun t => t ◇ z) (h x y z)))).trans (congrArg (fun t => ((x ◇ y) ◇ y) ◇ t) (congrArg (fun t => t ◇ z) ((h (x ◇ y) y z).symm)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59678_to_61351 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59678_to_61351
