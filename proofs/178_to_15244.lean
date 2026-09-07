-- Equation178 → Equation15244
-- Recorded verdict: true
-- Premise: x = (y ◇ y) ◇ (x ◇ z)
-- Conclusion: x = x ◇ (((x ◇ (y ◇ y)) ◇ x) ◇ x)
-- Original submission SHA-256: 46e276e8baae3876b46abcc206e709d010d3e0bdc0d5ee63c9387efabb09e8fa
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ (((x ◇ (y ◇ y)) ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q2)) ((h q0 q0 q0).symm)).symm).trans ((h q1 (q0 ◇ q0) q2).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ q3) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q5 q3 q3)).symm).trans (apc0 q4 q5 (q3 ◇ q3))
  exact ((apc1 x x x).symm).trans (apc1 x x (x ◇ (((x ◇ (y ◇ y)) ◇ x) ◇ x)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_178_to_15244 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_178_to_15244
