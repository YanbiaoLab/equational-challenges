-- Equation41450 → Equation41141
-- Recorded verdict: true
-- Premise: x = ((((y * z) * w) * z) * z) * x
-- Conclusion: x = ((((y * y) * z) * w) * z) * x
-- Original submission SHA-256: f620dea09b87d7b692bf776a1e392feddd0a6e0f84ad6879317eedb553790547
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((((y ◇ z) ◇ w) ◇ z) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((((y ◇ y) ◇ z) ◇ w) ◇ z) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc3 : forall (q0 q1:G), (q1 ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h q1 q0 q1 q1).symm)).symm).trans ((h q0 (q0 ◇ q1) q1 q1).symm)
  exact (apc3 x ((((y ◇ y) ◇ z) ◇ w) ◇ z)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41450_to_41141 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41450_to_41141
