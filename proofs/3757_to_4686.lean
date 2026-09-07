-- Equation3757 → Equation4686
-- Recorded verdict: true
-- Premise: x * y = (y * x) * (z * w)
-- Conclusion: (x * y) * z = (z * w) * x
-- Original submission SHA-256: 81d825d50daaa39f5a2f1d1ceffb5131e05c16b6a7557b646ad97fb22a25d8a1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ x) ◇ (z ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (z ◇ w) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc2 : forall (q0 q1 q2 q3 q4 q5:G), ((q3 ◇ q0) ◇ (q2 ◇ q1)) = ((q1 ◇ q2) ◇ (q5 ◇ q4)):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((congrArg (fun t => t ◇ (q5 ◇ q4)) ((h q1 q2 q3 q0).symm)).symm).trans ((h (q3 ◇ q0) (q2 ◇ q1) q5 q4).symm)).symm
  have apc3 : forall (q6 q7 q8 q9 q10 q11:G), ((q8 ◇ q11) ◇ (q7 ◇ q6)) = (q9 ◇ q10):=by
    intro q6 q7 q8 q9 q10 q11
    exact ((apc2 q9 q8 q11 q10 q6 q7).symm).trans ((h q9 q10 q11 q8).symm)
  have apc4 : forall (q6 q7 q8 q9 q10 q11:G), (q9 ◇ q10) = (q6 ◇ q6):=by
    intro q6 q7 q8 q9 q10 q11
    exact ((apc3 q6 q7 q8 q9 q10 q11).symm).trans (apc3 q6 q7 q8 q6 q6 q11)
  exact (apc4 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) (x ◇ y) z ((x ◇ y) ◇ z)).trans ((apc4 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) (z ◇ w) x ((x ◇ y) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3757_to_4686 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3757_to_4686
