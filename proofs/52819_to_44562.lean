-- Equation52819 → Equation44562
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * y)) * x) * u
-- Conclusion: x * y = y * ((y * (y * x)) * y)
-- Original submission SHA-256: ce029ee12f5bb6fc2a114e7920be6a2715eef55c60a0af7080579584906f92e7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (w ◇ y)) ◇ x) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = y ◇ ((y ◇ (y ◇ x)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q2 ◇ q4) ◇ q0) ◇ q1) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q1) ((h (q2 ◇ q4) q0 q0 q0 q3).symm)).symm).trans ((h q3 q4 (q0 ◇ (q0 ◇ q0)) q2 q1).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q5 ◇ (q6 ◇ q8)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((apc0 q7 q5 q5 q5 (q6 ◇ q8)).symm).trans ((h q7 q8 q5 q6 q5).symm)
  exact (apc1 y (y ◇ (y ◇ x)) x y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52819_to_44562 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52819_to_44562
