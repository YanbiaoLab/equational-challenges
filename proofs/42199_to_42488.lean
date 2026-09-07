-- Equation42199 → Equation42488
-- Recorded verdict: true
-- Premise: x * y = z * (z * (x * (z * w)))
-- Conclusion: x * x = y * (x * ((z * z) * z))
-- Original submission SHA-256: 0e8ae16686d5417f9185da0a163f07a8c2b183034012ae73026eb4f786f72d55
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (z ◇ (x ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((z ◇ z) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ (q3 ◇ (q0 ◇ q1))) = (q3 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q3 ◇ t) ((h q0 q1 q3 q0).symm))).symm).trans ((h q3 q2 q3 (q0 ◇ (q3 ◇ q0))).symm)
  have apc2 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc4 : forall (q4 q5 q6 q7:G), (q6 ◇ q4) = (q5 ◇ q5):=by
    intro q4 q5 q6 q7
    exact (((apc0 q5 (q6 ◇ q4) q4 q6).symm).trans ((h q5 q7 q6 q4).symm)).trans (apc2 q5 q7 (q5 ◇ q7) (q5 ◇ q7))
  exact (apc4 x (x ◇ x) x (x ◇ x)).trans ((apc4 (x ◇ ((z ◇ z) ◇ z)) (x ◇ x) y (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42199_to_42488 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42199_to_42488
