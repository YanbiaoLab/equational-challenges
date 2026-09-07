-- Equation20412 → Equation50670
-- Recorded verdict: true
-- Premise: x = (y * z) * ((w * (z * u)) * x)
-- Conclusion: x * y = (y * ((x * y) * z)) * y
-- Original submission SHA-256: 3a9827776b810197bba4818e54b15b61ff9c60b2ebc3cfdb4719a612d25800c7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ ((w ◇ (z ◇ u)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ ((x ◇ y) ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((q1 ◇ ((q5 ◇ q3) ◇ q0)) ◇ q2) = ((q4 ◇ q5) ◇ q2):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((congrArg (fun t => (q4 ◇ q5) ◇ t) ((h q2 q0 (q5 ◇ q3) q1 q0).symm)).symm).trans ((h ((q1 ◇ ((q5 ◇ q3) ◇ q0)) ◇ q2) q4 q5 q0 q3).symm)).symm
  have apc1 : forall (q6 q7 q8 q9:G), ((q8 ◇ q9) ◇ q7) = (q6 ◇ q7):=by
    intro q6 q7 q8 q9
    exact (((congrArg (fun t => t ◇ q7) ((h q6 q6 q6 q9 q6).symm)).symm).trans (apc0 q6 (q6 ◇ q6) q7 (q6 ◇ q6) q8 q9)).symm
  exact ((apc1 x y (x ◇ y) z).symm).trans ((apc1 ((x ◇ y) ◇ z) y y ((x ◇ y) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20412_to_50670 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20412_to_50670
