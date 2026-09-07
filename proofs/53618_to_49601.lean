-- Equation53618 → Equation49601
-- Recorded verdict: true
-- Premise: x * y = (((z * z) * y) * w) * x
-- Conclusion: x * x = (y * (z * (w * x))) * z
-- Original submission SHA-256: 9e6f0b0d9ba753410cab16ab10314986377cc4a0905f592056ac463b37665369
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ z) ◇ y) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ (z ◇ (w ◇ x))) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q1 ◇ (q0 ◇ q0)) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h q1 (q0 ◇ q0) q0 q3).symm)).symm).trans ((h q2 q3 (q0 ◇ q0) q1).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (q2 ◇ q3) = (q2 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q1 q2 q0)
  have apc2 : forall (q4 q5 q6 q7 q8:G), ((q6 ◇ (q5 ◇ q5)) ◇ q4) = (q7 ◇ q8):=by
    intro q4 q5 q6 q7 q8
    exact ((apc1 q4 q4 (q6 ◇ (q5 ◇ q5)) q7).symm).trans (apc0 q5 q6 q7 q8)
  have apc14 : forall (q4 q5 q6 q7 q8:G), (q7 ◇ q8) = (q4 ◇ q4):=by
    intro q4 q5 q6 q7 q8
    exact ((apc2 q4 q5 q6 q7 q8).symm).trans (apc2 q4 q5 q6 q4 q4)
  exact (apc14 (x ◇ x) (x ◇ x) (x ◇ x) x x).trans ((apc14 (x ◇ x) (x ◇ x) (x ◇ x) (y ◇ (z ◇ (w ◇ x))) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53618_to_49601 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53618_to_49601
