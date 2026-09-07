-- Equation53604 → Equation55309
-- Recorded verdict: true
-- Premise: x * y = (((z * z) * x) * w) * w
-- Conclusion: x * (y * z) = y * ((z * z) * y)
-- Original submission SHA-256: b902522caf6cbd9a132c25c47cc4dfb702103edfee1143f3c96b8703d29116e0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ z) ◇ x) ◇ w) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = y ◇ ((z ◇ z) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ q0) ◇ q2) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q2) ((h (q1 ◇ q1) q0 q1 q2).symm)).symm).trans ((h q2 q3 (q1 ◇ q1) q2).symm)).trans (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3))
  have apc2 : forall (q4 q5 q6:G), (q5 ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5 q6
    exact (((apc1 q4 q5 q4 (((q5 ◇ q5) ◇ q4) ◇ q4)).symm).trans ((((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) (apc1 (q4 ◇ q4) q4 q5 q4))).symm).trans ((h q5 q6 (q4 ◇ q4) q4).symm)).trans (apc0 q5 q6 (q5 ◇ q6) (q5 ◇ q6)))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc0 x (y ◇ z) x x
    _ = (y ◇ y):=apc2 y x x
    _ = (y ◇ ((z ◇ z) ◇ y)):=(apc0 y ((z ◇ z) ◇ y) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53604_to_55309 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53604_to_55309
