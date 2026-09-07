-- Equation5731 → Equation3716
-- Recorded verdict: true
-- Premise: x = x * (y * (z * ((y * w) * u)))
-- Conclusion: x * y = (x * x) * (y * z)
-- Original submission SHA-256: 4f1ee8d73af8350f4411189bb6c284bc87f4f4e0f2bdc508b5794ec1f5229934
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ (y ◇ (z ◇ ((y ◇ w) ◇ u)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ x) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h q1 q0 (q1 ◇ q0) q0 q0).symm)).symm).trans ((h q0 q1 q0 q0 ((q0 ◇ q0) ◇ q0)).symm)
  exact (calc
    (x ◇ y) = x:=apc0 x y
    _ = ((x ◇ x) ◇ (y ◇ z)):=(((congrArg (fun t => t ◇ (y ◇ z)) (apc0 x x)).trans (congrArg (fun t => x ◇ t) (apc0 y z))).trans (apc0 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5731_to_3716 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5731_to_3716
