-- Equation27736 → Equation54648
-- Recorded verdict: true
-- Premise: x = ((y ◇ (x ◇ x)) ◇ z) ◇ (w ◇ u)
-- Conclusion: x ◇ (y ◇ z) = w ◇ (u ◇ (x ◇ y))
-- Original submission SHA-256: 41a3c78ff5785a49f4df1ea064b40f745a8eb0cd0ae55a27f78269d9aca907c3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ (x ◇ x)) ◇ z) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = w ◇ (u ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ (q2 ◇ q1)) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q0 q0 (q3 ◇ q3) q0 q0).symm)).symm).trans ((h q3 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0) q2 q1).symm)
  exact (apc0 x z y (x ◇ (y ◇ z))).trans ((apc0 w (x ◇ y) u (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27736_to_54648 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27736_to_54648
