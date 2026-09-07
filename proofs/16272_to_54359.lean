-- Equation16272 → Equation54359
-- Recorded verdict: true
-- Premise: x = x * ((((y * z) * z) * w) * u)
-- Conclusion: x * (y * z) = x * (z * (w * y))
-- Original submission SHA-256: c0195ec5be2a3d5e1d9d401ace1a60676d3c0a45fbb4f8485839709667ba04e9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ ((((y ◇ z) ◇ z) ◇ w) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = x ◇ (z ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q1 ◇ (((q2 ◇ q3) ◇ q3) ◇ q0)) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q1 ◇ t) ((h (((q2 ◇ q3) ◇ q3) ◇ q0) q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 q3 q0 ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6 q7 q8 q9:G), (q5 ◇ (q6 ◇ q4)) = q5:=by
    intro q4 q5 q6 q7 q8 q9
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ q4) (apc0 q7 q6 q8 q9))).symm).trans (((congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ q4) (apc0 q7 (q6 ◇ (((q8 ◇ q9) ◇ q9) ◇ q7)) q8 q9))).symm).trans (apc0 q4 q5 q6 (((q8 ◇ q9) ◇ q9) ◇ q7)))
  exact (apc1 z x y (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).trans ((apc1 (w ◇ y) x z (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_16272_to_54359 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_16272_to_54359
