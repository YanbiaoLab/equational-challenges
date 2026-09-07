-- Equation14528 → Equation38149
-- Recorded verdict: true
-- Premise: x = x * (((y * z) * (w * y)) * u)
-- Conclusion: x = ((x * ((y * z) * x)) * x) * z
-- Original submission SHA-256: 109f40ee6676f4bf7ad59ab13332f75b307a367944041b4055fa4dd9f070295e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ (((y ◇ z) ◇ (w ◇ y)) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ ((y ◇ z) ◇ x)) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q1 ◇ ((q2 ◇ q3) ◇ q0)) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q0) ((h (q2 ◇ q3) q0 q0 q0 q2).symm))).symm).trans ((h q1 q2 q3 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ (q5 ◇ q6)) = q4:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q4 (q5 ◇ q6) q4 q4)).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) q4 q5 q6)
  have apc2 : forall (q7 q8:G), (q7 ◇ q8) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (apc1 q8 q7 q7)).symm).trans (apc1 q7 q8 (q7 ◇ q7))
  exact (calc
    x = x:=rfl
    _ = (((x ◇ ((y ◇ z) ◇ x)) ◇ x) ◇ z):=(((((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) (apc2 y z))))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (apc2 y x))))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (apc2 x y)))).trans (congrArg (fun t => t ◇ z) (apc2 x x))).trans (apc2 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14528_to_38149 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14528_to_38149
