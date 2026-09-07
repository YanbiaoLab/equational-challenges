-- Equation49183 → Equation3318
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * w) * (y * x)
-- Conclusion: x * y = x * (y * (y * x))
-- Original submission SHA-256: d8babddfabbeb46a4a90c66558aa14916f057871544785855c74464b3b7f2f47
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ w) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = x ◇ (y ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ (q3 ◇ q2)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) ((h q0 q1 q0 q3).symm)).symm).trans ((h q2 q3 (q0 ◇ q1) (q1 ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6 q7 q8 q9:G), (q4 ◇ (q7 ◇ q6)) = (q6 ◇ q5):=by
    intro q4 q5 q6 q7 q8 q9
    exact (((apc0 q8 q9 q6 q5).symm).trans ((((congrArg (fun t => (q8 ◇ q9) ◇ t) ((h q5 q6 q7 q4).symm)).symm).trans (apc0 q8 q9 (q6 ◇ q5) ((q7 ◇ q6) ◇ q4))).trans (apc0 q6 q5 q4 (q7 ◇ q6)))).symm
  exact ((apc1 (x ◇ y) y x x (x ◇ y) (x ◇ y)).symm).trans (apc1 (x ◇ y) (y ◇ (y ◇ x)) x x (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49183_to_3318 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49183_to_3318
