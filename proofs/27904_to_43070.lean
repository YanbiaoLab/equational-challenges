-- Equation27904 → Equation43070
-- Recorded verdict: true
-- Premise: x = ((y * (y * y)) * y) * (z * x)
-- Conclusion: x * y = z * (z * ((x * y) * y))
-- Original submission SHA-256: b5d0550b0f41eeb6bd3aae613693a04e962fdb478fb74c2bbdef8822dc5081c8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ y)) ◇ y) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (z ◇ ((x ◇ y) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ (q2 ◇ q2)) ◇ q2) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => ((q2 ◇ (q2 ◇ q2)) ◇ q2) ◇ t) ((h q0 q0 q1).symm)).symm).trans ((h (q1 ◇ q0) q2 ((q0 ◇ (q0 ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q0).symm).trans (apc0 q0 q0 q0)
  have apc2 : forall (q3 q4:G), (q3 ◇ (q4 ◇ q4)) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (apc1 q4 q3 (q3 ◇ q4))).symm).trans (((apc0 (q3 ◇ q4) q3 q3).symm).trans ((h q4 q3 q3).symm))
  exact (calc
    (x ◇ y) = (y ◇ y):=apc1 y x x
    _ = ((x ◇ y) ◇ y):=(apc1 y (x ◇ y) x).symm
    _ = (z ◇ (((x ◇ y) ◇ y) ◇ ((x ◇ y) ◇ y))):=(apc2 z ((x ◇ y) ◇ y)).symm
    _ = (z ◇ (z ◇ ((x ◇ y) ◇ y))):=(congrArg (fun t => z ◇ t) (apc1 ((x ◇ y) ◇ y) z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27904_to_43070 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27904_to_43070
