-- Equation42878 → Equation60012
-- Recorded verdict: true
-- Premise: x * y = y * (z * ((z * z) * z))
-- Conclusion: (x * x) * y = (x * y) * (y * y)
-- Original submission SHA-256: 08bfd82a85d043c58ffd61a241c9c623505a995f84072168e8ac744f75a64b7d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ ((z ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = (x ◇ y) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5:G), (q4 ◇ (q5 ◇ (q5 ◇ q5))) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => q5 ◇ t) ((apc0 (q5 ◇ q5) q5 q3).symm))).symm).trans ((h q3 q4 q5).symm)
  have apc4 : forall (q6 q7 q8 q9:G), (q8 ◇ (q7 ◇ (q7 ◇ q7))) = (q6 ◇ q9):=by
    intro q6 q7 q8 q9
    exact (((apc2 q6 q9 q7).symm).trans (apc1 q8 q9 (q7 ◇ (q7 ◇ q7)))).symm
  exact ((apc4 (x ◇ x) ((x ◇ x) ◇ y) ((x ◇ y) ◇ (y ◇ y)) y).symm).trans (apc4 (x ◇ y) ((x ◇ x) ◇ y) ((x ◇ y) ◇ (y ◇ y)) (y ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42878_to_60012 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42878_to_60012
