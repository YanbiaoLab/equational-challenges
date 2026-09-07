-- Equation28613 → Equation42716
-- Recorded verdict: true
-- Premise: x = (((y ◇ x) ◇ x) ◇ z) ◇ (w ◇ u)
-- Conclusion: x ◇ y = x ◇ (z ◇ ((y ◇ w) ◇ u))
-- Original submission SHA-256: a97a55b074457f3bbcbe648085d22c82133072d695f6a08fb802f8eea22f9f44
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ x) ◇ x) ◇ z) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = x ◇ (z ◇ ((y ◇ w) ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ q0)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q0)) ((h q2 q0 q2 q0 q0).symm)).symm).trans ((h q2 (q0 ◇ q2) (q0 ◇ q0) q1 q0).symm)
  have apc1 : forall (q3 q4 q5 q6 q7 q8:G), (q5 ◇ q6) = (q4 ◇ q3):=by
    intro q3 q4 q5 q6 q7 q8
    exact (((congrArg (fun t => t ◇ (q7 ◇ q8)) (congrArg (fun t => t ◇ q6) (apc0 q3 q4 q5))).trans (apc0 q8 q7 (q5 ◇ q6))).symm).trans (((congrArg (fun t => t ◇ (q7 ◇ q8)) (congrArg (fun t => t ◇ q6) (apc0 q3 q4 (q5 ◇ (q4 ◇ q3))))).symm).trans ((h (q4 ◇ q3) q5 q6 q7 q8).symm))
  have apc2 : forall (q3 q4 q8 q7 q5 q6:G), (q5 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q8 q7 q5 q6
    exact (((apc1 q3 q4 q5 q6 q7 q8).symm).trans (apc1 q5 q5 q5 q6 q7 q8)).symm
  exact ((apc2 y x (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).symm).trans (apc2 (z ◇ ((y ◇ w) ◇ u)) x (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_28613_to_42716 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_28613_to_42716
