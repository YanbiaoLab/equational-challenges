-- Equation42012 → Equation42519
-- Recorded verdict: true
-- Premise: x * y = y * (z * (w * (x * u)))
-- Conclusion: x * x = y * (y * ((z * y) * x))
-- Original submission SHA-256: 8e13d8f7738b92f2dd07a4564be002b13007f13e8ec0fd38e8e14829e5ee0de4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ (z ◇ (w ◇ (x ◇ u)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ ((z ◇ y) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (q4 ◇ (q0 ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q4 ◇ t) ((h q0 q1 q2 q0 q0).symm))).symm).trans ((h q2 q3 q4 q1 (q0 ◇ (q0 ◇ q0))).symm)
  have apc3 : forall (q0 q1 q2 q3 q4:G), (q2 ◇ q3) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).symm).trans (apc0 q0 q1 q0 q3 q4)
  have apc4 : forall (q5 q6 q7 q8 q9 q10:G), (q5 ◇ (q10 ◇ (q6 ◇ q7))) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((apc3 q5 q5 q9 (q10 ◇ (q6 ◇ q7)) q5).symm).trans (apc0 q6 q7 q8 q9 q10)
  have apc7 : forall (q5 q6 q7 q8 q9 q10:G), (q8 ◇ q9) = (q5 ◇ q5):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((apc4 q5 q6 q7 q8 q9 q10).symm).trans (apc4 q5 q6 q7 q5 q5 q10)
  exact (apc7 (x ◇ x) (x ◇ x) (x ◇ x) x x (x ◇ x)).trans ((apc7 (x ◇ x) (x ◇ x) (x ◇ x) y (y ◇ ((z ◇ y) ◇ x)) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42012_to_42519 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42012_to_42519
