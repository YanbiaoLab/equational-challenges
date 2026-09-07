-- Equation52604 → Equation3606
-- Recorded verdict: true
-- Premise: x * y = ((z * (x * z)) * w) * x
-- Conclusion: x * y = z * ((y * y) * w)
-- Original submission SHA-256: 95e9b84622b8df84097f471615acee2fb5aea0c8b4a2ada13879ac1152249a4b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (x ◇ z)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((y ◇ y) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ q0) ◇ ((q2 ◇ q2) ◇ q0)) = (q3 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((h q3 q1 q2 q0).trans (apc0 ((q2 ◇ (q3 ◇ q2)) ◇ q0) q3 q0 q0)).trans ((congrArg (fun t => t ◇ ((q2 ◇ (q3 ◇ q2)) ◇ q0)) (congrArg (fun t => t ◇ q0) (apc0 q2 (q3 ◇ q2) (q2 ◇ (q3 ◇ q2)) (q2 ◇ (q3 ◇ q2))))).trans (congrArg (fun t => ((q2 ◇ q2) ◇ q0) ◇ t) (congrArg (fun t => t ◇ q0) (apc0 q2 (q3 ◇ q2) (q2 ◇ (q3 ◇ q2)) (q2 ◇ (q3 ◇ q2))))))).symm
  exact ((apc1 (z ◇ ((y ◇ y) ◇ w)) y (x ◇ y) x).symm).trans (apc1 (z ◇ ((y ◇ y) ◇ w)) ((y ◇ y) ◇ w) (x ◇ y) z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52604_to_3606 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52604_to_3606
