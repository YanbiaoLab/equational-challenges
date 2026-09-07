-- Equation50073 → Equation53591
-- Recorded verdict: true
-- Premise: x * y = (z * (y * (w * w))) * w
-- Conclusion: x * y = (((z * z) * x) * x) * z
-- Original submission SHA-256: 22b1d2914b7766f3917b44fd04c4b153db3ff6b5c2b8abd194711f4270bb27e0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (y ◇ (w ◇ w))) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((z ◇ z) ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q2) ((h q0 q1 q0 (q4 ◇ (q2 ◇ q2))).symm)).symm).trans ((h q3 q4 (q0 ◇ (q1 ◇ ((q4 ◇ (q2 ◇ q2)) ◇ (q4 ◇ (q2 ◇ q2))))) q2).symm)
  have apc13 : forall (q5 q6 q7 q8:G), ((q5 ◇ q5) ◇ q6) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ q6) ((apc0 q5 q5 q5 q5).symm)).symm).trans (apc1 q5 q5 q6 q7 q8)
  exact ((apc13 (x ◇ y) ((((z ◇ z) ◇ x) ◇ x) ◇ z) x y).symm).trans (apc13 (x ◇ y) ((((z ◇ z) ◇ x) ◇ x) ◇ z) (((z ◇ z) ◇ x) ◇ x) z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50073_to_53591 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50073_to_53591
