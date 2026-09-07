-- Equation36193 → Equation53380
-- Recorded verdict: true
-- Premise: x = ((y * (z * w)) * (z * w)) * x
-- Conclusion: x * y = (((y * z) * y) * y) * y
-- Original submission SHA-256: 8a085107d224bed571647fedee370a93f6e6bf1f02b9b9ea4dce28ac9df5c904
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ w)) ◇ (z ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((y ◇ z) ◇ y) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ q0) q0 q2 q0).symm)).symm).trans ((h q1 (q0 ◇ (q2 ◇ q0)) q2 q0).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ q4) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (apc0 q3 q3 q3)).symm).trans (apc0 q3 q4 (q3 ◇ q3))
  exact (apc1 x y).trans ((apc1 (((y ◇ z) ◇ y) ◇ y) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_36193_to_53380 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_36193_to_53380
