-- Equation44954 → Equation54437
-- Recorded verdict: true
-- Premise: x * y = z * ((w * (z * y)) * y)
-- Conclusion: x * (y * z) = y * (z * (w * z))
-- Original submission SHA-256: 03d9729dc7ab9a44c4251ed924a93500b1ebe5202ca9d9c739f0a6ca01163e99
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ (z ◇ y)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = y ◇ (z ◇ (w ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc1 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q6 ◇ (q3 ◇ q5)) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc0 q3 (q3 ◇ (q6 ◇ q5)) q5)).symm).trans ((h q4 q5 q6 q3).symm)
  have apc4 : forall (q7 q8 q9:G), (q8 ◇ (q7 ◇ q9)) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact (apc2 q7 q7 q9 q8).trans ((apc1 q7 q9 q7 q7).symm)
  exact (calc
    (x ◇ (y ◇ z)) = (z ◇ z):=apc4 y x z
    _ = (y ◇ (z ◇ (w ◇ z))):=((congrArg (fun t => y ◇ t) (apc4 w z z)).trans (apc4 z y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44954_to_54437 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44954_to_54437
