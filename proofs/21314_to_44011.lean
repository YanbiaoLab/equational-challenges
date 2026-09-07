-- Equation21314 → Equation44011
-- Recorded verdict: true
-- Premise: x = (y * z) * (((w * w) * w) * u)
-- Conclusion: x * y = z * ((z * w) * (w * w))
-- Original submission SHA-256: f8ea6db3006f9382ff63801f4df24f3ddfc3e73a4a0a064f0b258461b937ced2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (((w ◇ w) ◇ w) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((z ◇ w) ◇ (w ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ (((q2 ◇ q2) ◇ q2) ◇ q1)) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (((q2 ◇ q2) ◇ q2) ◇ q1)) ((h q0 q0 q0 q0 q0).symm)).symm).trans ((h q3 (q0 ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ q0) q2 q1).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ q4) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (apc0 ((q4 ◇ q4) ◇ q4) q4 q4 q4)).symm).trans (apc0 q5 (((q4 ◇ q4) ◇ q4) ◇ q4) q4 q6)
  exact (apc1 y x (x ◇ y)).trans ((apc1 ((z ◇ w) ◇ (w ◇ w)) z (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21314_to_44011 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21314_to_44011
