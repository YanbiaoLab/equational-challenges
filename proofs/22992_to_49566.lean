-- Equation22992 → Equation49566
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ w)) ◇ ((x ◇ u) ◇ y)
-- Conclusion: x ◇ x = (y ◇ (z ◇ (y ◇ x))) ◇ y
-- Original submission SHA-256: a2fddef9390b1a1ccf9dae1b159a4ea90ebacdcbf04cc671c57b8f09d1435ee2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ w)) ◇ ((x ◇ u) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (z ◇ (y ◇ x))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5 q6:G), ((q5 ◇ (q6 ◇ q4)) ◇ (q1 ◇ q5)) = (q2 ◇ (q3 ◇ q0)):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ (q6 ◇ q4)) ◇ t) (congrArg (fun t => t ◇ q5) ((h q1 q2 q3 q0 q0).symm))).symm).trans ((h (q2 ◇ (q3 ◇ q0)) q5 q6 q4 ((q1 ◇ q0) ◇ q2)).symm)
  have apc1 : forall (q7 q8 q9 q10 q11 q12:G), ((q11 ◇ (q12 ◇ q10)) ◇ (q8 ◇ q11)) = (q9 ◇ q7):=by
    intro q7 q8 q9 q10 q11 q12
    exact (((congrArg (fun t => q9 ◇ t) ((h q7 q7 q7 q7 q7).symm)).symm).trans ((apc0 ((q7 ◇ q7) ◇ q7) q8 q9 (q7 ◇ (q7 ◇ q7)) q10 q11 q12).symm)).symm
  have apc3 : forall (q7 q8 q9 q10 q11 q12:G), (q9 ◇ q7) = (q8 ◇ q8):=by
    intro q7 q8 q9 q10 q11 q12
    exact ((apc1 q7 q8 q9 q10 q11 q12).symm).trans (apc1 q8 q8 q8 q10 q11 q12)
  exact (apc3 x (x ◇ x) x (x ◇ x) (x ◇ x) (x ◇ x)).trans ((apc3 y (x ◇ x) (y ◇ (z ◇ (y ◇ x))) (x ◇ x) (x ◇ x) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22992_to_49566 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22992_to_49566
