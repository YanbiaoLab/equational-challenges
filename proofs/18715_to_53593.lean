-- Equation18715 → Equation53593
-- Recorded verdict: true
-- Premise: x = (y * z) * (w * ((u * u) * y))
-- Conclusion: x * y = (((z * z) * x) * y) * x
-- Original submission SHA-256: e7a5d3a403243e6ac106db72adc49becde261a11061969e1d4203773daa78502
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (w ◇ ((u ◇ u) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((z ◇ z) ◇ x) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((((q0 ◇ q0) ◇ q2) ◇ q4) ◇ q1) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (((q0 ◇ q0) ◇ q2) ◇ q4) ◇ t) ((h q1 q2 q0 (q0 ◇ q0) q0).symm)).symm).trans ((h q3 ((q0 ◇ q0) ◇ q2) q4 (q2 ◇ q0) q0).symm)
  have apc3 : forall (q5 q6 q7:G), (q5 ◇ q6) = q7:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q6) (apc0 q5 q5 (q5 ◇ q5) q5 q5)).symm).trans (apc0 (q5 ◇ q5) q6 q5 q7 q5)
  exact (apc3 x y (x ◇ y)).trans ((apc3 (((z ◇ z) ◇ x) ◇ y) x (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18715_to_53593 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18715_to_53593
