-- Equation44881 → Equation3687
-- Recorded verdict: true
-- Premise: x * y = z * ((z * (w * z)) * y)
-- Conclusion: x * x = (y * y) * (y * x)
-- Original submission SHA-256: db1aa9037429bbcffc3998f9e00a2c0944c087a5ee6b426842227b500f617c65
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((z ◇ (w ◇ z)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (y ◇ y) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ q1)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((apc0 (q2 ◇ (q0 ◇ q2)) q1 q0 q0).symm)).symm).trans ((h q0 q1 q2 q0).symm)
  have apc10 : forall (q3 q4 q5 q6:G), (q6 ◇ (q3 ◇ q5)) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc0 q3 q5 q3 q3)).symm).trans (apc1 q4 q5 q6)
  exact (apc10 y x x (y ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44881_to_3687 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44881_to_3687
