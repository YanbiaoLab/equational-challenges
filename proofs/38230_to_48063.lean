-- Equation38230 → Equation48063
-- Recorded verdict: true
-- Premise: x = ((y * ((x * x) * x)) * z) * x
-- Conclusion: x * y = (y * (y * x)) * (y * y)
-- Original submission SHA-256: 9e8216a0adc9c6d811a6fb9e70d3a98b31e1fd21d18482b17c9ab9fde62bfac7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ ((x ◇ x) ◇ x)) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ (y ◇ x)) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1:G), (q1 ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h q1 q0 ((q0 ◇ q0) ◇ q0)).symm)).symm).trans ((h q0 (q0 ◇ ((q1 ◇ q1) ◇ q1)) q1).symm)
  exact (calc
    (x ◇ y) = y:=apc0 y x
    _ = ((y ◇ (y ◇ x)) ◇ (y ◇ y)):=((((congrArg (fun t => t ◇ (y ◇ y)) (congrArg (fun t => y ◇ t) (apc0 x y))).trans (congrArg (fun t => t ◇ (y ◇ y)) (apc0 x y))).trans (congrArg (fun t => x ◇ t) (apc0 y y))).trans (apc0 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38230_to_48063 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38230_to_48063
