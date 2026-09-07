-- Equation46125 → Equation47878
-- Recorded verdict: true
-- Premise: x * y = (x * x) * (x * (z * z))
-- Conclusion: x * y = (x * (x * x)) * (z * y)
-- Original submission SHA-256: a34d8fe243f4956bddb4c61c3c0d58623a89e793e01a1fa2acffacc40fc688ac
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ x) ◇ (x ◇ (z ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ (x ◇ x)) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((apc0 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)) q0).symm).trans ((h q0 q1 q0).symm)).trans (apc0 q0 q1 (q0 ◇ q1))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc0 x y (x ◇ y)
    _ = ((x ◇ (x ◇ x)) ◇ (z ◇ y)):=(((congrArg (fun t => t ◇ (z ◇ y)) (apc0 x (x ◇ x) (x ◇ (x ◇ x)))).trans (apc0 (x ◇ x) (z ◇ y) ((x ◇ x) ◇ (z ◇ y)))).trans (apc1 x ((x ◇ x) ◇ (x ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46125_to_47878 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46125_to_47878
