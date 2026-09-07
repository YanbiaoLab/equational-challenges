-- Equation14825 → Equation48047
-- Recorded verdict: true
-- Premise: x = y * (((y * z) * (w * x)) * u)
-- Conclusion: x * y = (y * (x * z)) * (y * y)
-- Original submission SHA-256: 160a5ff08a6a9e9fc1a21d6d89fd028db05f7e78bf49e3e4656a183e9270c923
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (((y ◇ z) ◇ (w ◇ x)) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ z)) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 ((q2 ◇ q0) ◇ (q0 ◇ q1)) q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0 (((((q2 ◇ q0) ◇ (q0 ◇ q1)) ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)).symm)
  exact (apc0 y (x ◇ y) x).trans ((apc0 (y ◇ y) (x ◇ y) (y ◇ (x ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14825_to_48047 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14825_to_48047
