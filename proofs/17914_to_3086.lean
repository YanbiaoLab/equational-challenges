-- Equation17914 → Equation3086
-- Recorded verdict: true
-- Premise: x = (x * y) * (x * ((y * x) * z))
-- Conclusion: x = (((x * y) * z) * x) * y
-- Original submission SHA-256: 1dfe8254b63e18e03fff0c0a41432874216b6c98514dbbc2f0414ea6289f9fc7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (x ◇ ((y ◇ x) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ z) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) (congrArg (fun t => q0 ◇ t) ((h q1 q0 q0).symm))).symm).trans ((h q0 q1 (q1 ◇ ((q0 ◇ q1) ◇ q0))).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ q3) = (q2 ◇ q2):=by
    intro q2 q3
    exact (((congrArg (fun t => q2 ◇ t) (apc0 q2 q3)).symm).trans (((congrArg (fun t => t ◇ ((q2 ◇ q3) ◇ (q2 ◇ q3))) (apc0 q2 q3)).symm).trans (apc0 (q2 ◇ q3) (q2 ◇ q3)))).symm
  have apc2 : forall (x y z q2 q3:G), ((x ◇ x) ◇ (x ◇ x)) = x:=by
    intro x y z q2 q3
    exact ((h x x x).trans ((congrArg (fun t => t ◇ (x ◇ ((x ◇ x) ◇ x))) (apc1 x x)).trans (congrArg (fun t => (x ◇ x) ◇ t) (apc1 x ((x ◇ x) ◇ x))))).symm
  exact (calc
    x = ((x ◇ x) ◇ (x ◇ x)):=(apc2 x x x x x).symm
    _ = ((x ◇ x) ◇ y):=(apc1 (x ◇ x) y).symm
    _ = ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ y):=congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ x) ((apc2 x x x x x).symm))
    _ = ((((x ◇ x) ◇ z) ◇ x) ◇ y):=(congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ x) (apc1 (x ◇ x) z))).symm
    _ = ((((x ◇ y) ◇ z) ◇ x) ◇ y):=(congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (apc1 x y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17914_to_3086 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_17914_to_3086
