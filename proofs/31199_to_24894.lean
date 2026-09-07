-- Equation31199 → Equation24894
-- Recorded verdict: true
-- Premise: x = (x * ((y * z) * (w * w))) * z
-- Conclusion: x = (x * (x * (y * y))) * (y * x)
-- Original submission SHA-256: f60e994cca67b629dadcf8e8c90bfe32b5804a00d883638332e0094a80f10452
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ z) ◇ (w ◇ w))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (x ◇ (y ◇ y))) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q0 ◇ (q1 ◇ q1))) ◇ q3) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q1)) ((h q0 q0 q3 q0).symm)))).symm).trans ((h q2 (q0 ◇ ((q0 ◇ q3) ◇ (q0 ◇ q0))) q3 q1).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q6 ◇ (q5 ◇ q4)) ◇ q7) = q6:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ q7) (congrArg (fun t => q6 ◇ t) (congrArg (fun t => q5 ◇ t) (apc0 q4 q4 q4 (q4 ◇ (q4 ◇ (q4 ◇ q4))))))).symm).trans (apc0 q5 (q4 ◇ (q4 ◇ (q4 ◇ q4))) q6 q7)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (x ◇ (y ◇ y))) ◇ (y ◇ x)):=(apc1 (y ◇ y) x x (y ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31199_to_24894 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31199_to_24894
