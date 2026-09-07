-- Equation38500 → Equation38898
-- Recorded verdict: true
-- Premise: x = ((y * ((y * z) * w)) * x) * x
-- Conclusion: x = (((x * x) * (x * x)) * x) * x
-- Original submission SHA-256: f9d9ae2ab2c374c4b9cc79f4e979f29045462b6ab33ec78982e65a1ccbf6a16a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ ((y ◇ z) ◇ w)) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((((q1 ◇ ((q1 ◇ q2) ◇ q0)) ◇ q3) ◇ q4) ◇ q4) = q4:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) (congrArg (fun t => (q1 ◇ ((q1 ◇ q2) ◇ q0)) ◇ t) ((h q3 q1 q2 q0).symm)))).symm).trans ((h q4 (q1 ◇ ((q1 ◇ q2) ◇ q0)) q3 q3).symm)
  have apc1 : forall (q5:G), (q5 ◇ q5) = q5:=by
    intro q5
    exact ((congrArg (fun t => t ◇ q5) ((h q5 q5 q5 q5).symm)).symm).trans (apc0 q5 q5 q5 q5 q5)
  exact (calc
    x = x:=rfl
    _ = ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ x):=(((((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ (x ◇ x)) (apc1 x)))).trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (apc1 x))))).trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc1 x)))).trans (congrArg (fun t => t ◇ x) (apc1 x))).trans (apc1 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38500_to_38898 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38500_to_38898
