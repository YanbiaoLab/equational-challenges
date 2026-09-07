-- Equation3892 → Equation53038
-- Recorded verdict: true
-- Premise: x ◇ x = (y ◇ (y ◇ y)) ◇ z
-- Conclusion: x ◇ x = (((y ◇ y) ◇ y) ◇ z) ◇ w
-- Original submission SHA-256: 7f7be40d066d7bdc4d6b39bb31e76012eb315031adf295a0c5aafa969f204368
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (y ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (((y ◇ y) ◇ y) ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ q2) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) ((h q0 q0 ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) q2).symm)
  exact (((p0 w x w).symm).trans (congrArg (fun t => t ◇ w) ((p0 x w z).symm))).trans ((congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ z) (p0 y x y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3892_to_53038 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3892_to_53038
