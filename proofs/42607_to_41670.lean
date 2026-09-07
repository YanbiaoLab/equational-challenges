-- Equation42607 → Equation41670
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (z ◇ ((w ◇ u) ◇ u))
-- Conclusion: x ◇ x = y ◇ (z ◇ (x ◇ (w ◇ w)))
-- Original submission SHA-256: 3c60b1b87dafc6fbbc2bd03b761c9ef8232f1912e4d4ca29ba48290dd9d5b7d5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ (z ◇ ((w ◇ u) ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ (x ◇ (w ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)) q0 q0).symm)).symm).trans ((h q1 q2 q0 q0 ((q0 ◇ q0) ◇ q0)).symm)
  exact (((p0 w x y).symm).trans (congrArg (fun t => y ◇ t) ((p0 x w z).symm))).trans ((congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (p0 w x x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42607_to_41670 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42607_to_41670
