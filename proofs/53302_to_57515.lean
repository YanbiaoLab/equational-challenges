-- Equation53302 → Equation57515
-- Recorded verdict: true
-- Premise: x * y = (((y * x) * y) * z) * z
-- Conclusion: x * (x * y) = ((z * w) * u) * w
-- Original submission SHA-256: a308a4ece150f4b76749f072bbb91ba16df22d7294879e1e455b6ae073bedc9e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((y ◇ x) ◇ y) ◇ z) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (x ◇ y) = ((z ◇ w) ◇ u) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q0)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ (q1 ◇ q0)) ((h q0 q1 (q1 ◇ q0)).symm)).symm).trans ((h q1 (q1 ◇ q0) (q1 ◇ q0)).symm)
  have apc16 : forall (q2 q3:G), ((q3 ◇ (q3 ◇ (q3 ◇ q2))) ◇ (q3 ◇ (q3 ◇ q2))) = (q2 ◇ q3):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ (q3 ◇ q2))) (apc0 (q3 ◇ q2) q3)).symm).trans ((h q2 q3 (q3 ◇ (q3 ◇ q2))).symm)
  have apc22 : forall (q4 q5 q6:G), (q4 ◇ ((q6 ◇ q5) ◇ q6)) = (q5 ◇ q6):=by
    intro q4 q5 q6
    exact ((apc16 q4 ((q6 ◇ q5) ◇ q6)).symm).trans ((h q5 q6 (((q6 ◇ q5) ◇ q6) ◇ (((q6 ◇ q5) ◇ q6) ◇ q4))).symm)
  have apc40 : forall (q7 q8 q9 q10:G), (q9 ◇ q10) = (q7 ◇ q8):=by
    intro q7 q8 q9 q10
    exact (((apc22 (((q10 ◇ q9) ◇ q10) ◇ ((q8 ◇ q7) ◇ q8)) q7 q8).symm).trans ((h q9 q10 ((q8 ◇ q7) ◇ q8)).symm)).symm
  exact (apc40 (x ◇ (x ◇ y)) (((z ◇ w) ◇ u) ◇ w) x (x ◇ y)).trans ((apc40 (x ◇ (x ◇ y)) (((z ◇ w) ◇ u) ◇ w) ((z ◇ w) ◇ u) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53302_to_57515 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53302_to_57515
