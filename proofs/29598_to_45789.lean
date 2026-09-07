-- Equation29598 → Equation45789
-- Recorded verdict: true
-- Premise: x = (y * (x * (z * (w * w)))) * u
-- Conclusion: x * y = z * (((w * x) * w) * y)
-- Original submission SHA-256: 9b1a63990344eda380426669c4e72c4d9b09267d10af54bacda7a1b834c09b09
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (x ◇ (z ◇ (w ◇ w)))) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((w ◇ x) ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ q1) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h q0 q0 q0 q0 (q2 ◇ (q0 ◇ (q0 ◇ q0)))).symm)).symm).trans ((h q2 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) q0 q0 q1).symm)
  exact (apc0 x y (x ◇ y)).trans ((apc0 z (((w ◇ x) ◇ w) ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29598_to_45789 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29598_to_45789
