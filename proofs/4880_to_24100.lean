-- Equation4880 → Equation24100
-- Recorded verdict: true
-- Premise: x = x * (y * (z * (w * (y * w))))
-- Conclusion: x = ((x * y) * y) * ((z * x) * z)
-- Original submission SHA-256: 77d7decc5bc83e37f5f4156efae6b76c94dca4d1b9bf561b9de651e823ec85b7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (z ◇ (w ◇ (y ◇ w))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ y) ◇ ((z ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h q1 q0 (q0 ◇ q1) q1).symm)).symm).trans ((h q0 q1 q0 (q0 ◇ q1)).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ y) ◇ ((z ◇ x) ◇ z)):=(((((congrArg (fun t => t ◇ ((z ◇ x) ◇ z)) (congrArg (fun t => t ◇ y) (apc0 x y))).trans (congrArg (fun t => (x ◇ y) ◇ t) (congrArg (fun t => t ◇ z) (apc0 z x)))).trans (congrArg (fun t => t ◇ (z ◇ z)) (apc0 x y))).trans (congrArg (fun t => x ◇ t) (apc0 z z))).trans (apc0 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4880_to_24100 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4880_to_24100
