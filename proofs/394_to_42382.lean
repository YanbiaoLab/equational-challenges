-- Equation394 → Equation42382
-- Recorded verdict: true
-- Premise: x * y = (z * x) * x
-- Conclusion: x * y = z * (w * (u * (z * y)))
-- Original submission SHA-256: e814f2ab75302520f37710143aac36424a615eab7e2478b1914837fd4dd2aeb0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (u ◇ (z ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact (((h q2 q0 q1).trans (apc0 (q1 ◇ q2) q2 q0)).trans ((congrArg (fun t => t ◇ (q1 ◇ q2)) (apc0 q1 q2 (q1 ◇ q2))).trans (congrArg (fun t => (q1 ◇ q1) ◇ t) (apc0 q1 q2 (q1 ◇ q2))))).symm
  exact ((apc1 y (x ◇ y) x).symm).trans (apc1 (w ◇ (u ◇ (z ◇ y))) (x ◇ y) z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_394_to_42382 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_394_to_42382
