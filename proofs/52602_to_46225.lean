-- Equation52602 → Equation46225
-- Recorded verdict: true
-- Premise: x * y = ((z * (x * z)) * z) * z
-- Conclusion: x * y = (x * z) * (z * (x * x))
-- Original submission SHA-256: 53870e67461a31f110d6a56bccd948efe5faee98df802fca66ca823ed3732f7c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (x ◇ z)) ◇ z) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ z) ◇ (z ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q1) ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) (apc0 q1 (q0 ◇ q1) q0))).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  have apc3 : forall (q3 q4 q5:G), (((q4 ◇ q4) ◇ q4) ◇ q4) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) (apc0 q4 (((q5 ◇ q5) ◇ q5) ◇ q5) (q4 ◇ (((q5 ◇ q5) ◇ q5) ◇ q5))))).symm).trans (((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) (congrArg (fun t => q4 ◇ t) ((apc1 q4 q5 q5).symm)))).symm).trans ((h q4 q3 q4).symm))
  have apc6 : forall (q6 q7 q8:G), (q8 ◇ q6) = (q7 ◇ q7):=by
    intro q6 q7 q8
    exact ((apc3 q6 q8 q6).symm).trans (apc1 q7 q8 q6)
  exact (apc6 y (x ◇ y) x).trans ((apc6 (z ◇ (x ◇ x)) (x ◇ y) (x ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52602_to_46225 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52602_to_46225
