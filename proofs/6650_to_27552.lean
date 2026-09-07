-- Equation6650 → Equation27552
-- Recorded verdict: true
-- Premise: x = x * (y * ((z * w) * (u * u)))
-- Conclusion: x = ((x * (y * x)) * x) * (y * x)
-- Original submission SHA-256: 09cb2ccaa865fac44de9b95d5452a6068a09415777fd2d7ffb220b0942d3621c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ (y ◇ ((z ◇ w) ◇ (u ◇ u)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h q1 (q0 ◇ q0) q0 q0 q0).symm)).symm).trans ((h q0 q1 q0 q0 (q0 ◇ q0)).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ x)):=(((((congrArg (fun t => t ◇ (y ◇ x)) (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (apc0 y x)))).trans (congrArg (fun t => t ◇ (y ◇ x)) (congrArg (fun t => t ◇ x) (apc0 x y)))).trans (congrArg (fun t => t ◇ (y ◇ x)) (apc0 x x))).trans (congrArg (fun t => x ◇ t) (apc0 y x))).trans (apc0 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6650_to_27552 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6650_to_27552
