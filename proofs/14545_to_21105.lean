-- Equation14545 → Equation21105
-- Recorded verdict: true
-- Premise: x = y * (((x * x) * (x * x)) * x)
-- Conclusion: x = (y * z) * (((y * z) * z) * x)
-- Original submission SHA-256: 18bc89927e7d6c7e64d7b8a77f06acc61d52f2c5a735e96d8b76d7cadf678bf1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (((y ◇ z) ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1
    exact (((congrArg (fun t => q1 ◇ t) ((h q0 (((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) ◇ ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)))).symm)).symm).trans ((h (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) q1).symm)).symm
  have apc1 : forall (q2 q3 q4:G), (q4 ◇ (q2 ◇ q3)) = q3:=by
    intro q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q3 q2)).symm).trans ((h q3 q4).symm)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ z) ◇ (((y ◇ z) ◇ z) ◇ x)):=(apc1 ((y ◇ z) ◇ z) x (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14545_to_21105 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14545_to_21105
