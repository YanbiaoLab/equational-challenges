-- Equation48206 → Equation48629
-- Recorded verdict: true
-- Premise: x * y = (z * (x * y)) * (w * u)
-- Conclusion: x * x = ((y * x) * z) * (w * x)
-- Original submission SHA-256: b57168b0dcc784e08e3c0ff82530347f506ab5c2ac2d2985e16c10d0e11fbe5b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (x ◇ y)) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = ((y ◇ x) ◇ z) ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((q0 ◇ q1) ◇ (q3 ◇ q2)) = (q4 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) ((h q0 q1 q0 q4 q5).symm)).symm).trans ((h q4 q5 (q0 ◇ (q0 ◇ q1)) q3 q2).symm)
  have apc2 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ q5) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc0 q0 q1 q2 q3 q4 q5).symm).trans (apc0 q0 q1 q2 q3 q0 q0)
  exact (apc2 (x ◇ x) (x ◇ x) (x ◇ x) (x ◇ x) x x).trans ((apc2 (x ◇ x) (x ◇ x) (x ◇ x) (x ◇ x) ((y ◇ x) ◇ z) (w ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48206_to_48629 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48206_to_48629
