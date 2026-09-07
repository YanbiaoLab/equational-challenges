-- Equation47029 → Equation51380
-- Recorded verdict: true
-- Premise: x * y = (x * x) * ((z * w) * w)
-- Conclusion: x * y = ((x * x) * (x * x)) * y
-- Original submission SHA-256: 0d81f086b9aafde9f93ec6d787092313813d6787e52b3cb70a78f9b1ed637d54
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ x) ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = ((x ◇ x) ◇ (x ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q2 ◇ q1) ◇ q1)) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((apc0 q0 q3 (q0 ◇ q3) (q0 ◇ q3)).symm).trans ((h q0 q3 q0 q0).trans (h (q0 ◇ q0) ((q0 ◇ q0) ◇ q0) q2 q1))).symm
  have apc2 : forall (q4 q5:G), ((q4 ◇ q4) ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5
    exact (((apc1 q4 q4 q4 q4).symm).trans ((h (q4 ◇ q4) q5 q4 q4).symm)).symm
  exact (calc
    (x ◇ y) = (x ◇ x):=apc0 x y (x ◇ y) (x ◇ y)
    _ = (((x ◇ x) ◇ (x ◇ x)) ◇ y):=((congrArg (fun t => t ◇ y) (apc2 x (x ◇ x))).trans (apc2 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47029_to_51380 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47029_to_51380
