-- Equation47397 → Equation62044
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((y * y) * w)
-- Conclusion: (x * y) * x = ((z * w) * w) * y
-- Original submission SHA-256: bbc66e830bfc01b080c0bd6d8302ecdec4fa3ebf28803cedf410576bfd50b0bc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ ((y ◇ y) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = ((z ◇ w) ◇ w) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ (q0 ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ q2) ◇ t) ((h q0 q2 q2 q0).symm)).symm).trans ((h q1 q2 q3 ((q2 ◇ q2) ◇ q0)).symm)
  have apc6 : forall (q4 q5 q6 q7 q8:G), ((q8 ◇ q7) ◇ (q4 ◇ q5)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => (q8 ◇ q7) ◇ t) (apc1 q4 (q7 ◇ q7) q5)).symm).trans ((h q6 q7 q8 q5).symm)
  have apc7 : forall (q9 q10 q11:G), ((q10 ◇ q11) ◇ (q9 ◇ q11)) = (q11 ◇ q11):=by
    intro q9 q10 q11
    exact (apc2 q9 q9 q11 q10).trans ((apc0 q9 q11 q9 q9).symm)
  have apc8 : forall (q12 q13 q14 q15:G), (q13 ◇ q14) = (q12 ◇ q12):=by
    intro q12 q13 q14 q15
    exact (((apc6 q15 q12 q13 q14 q15).symm).trans ((apc0 (q15 ◇ q14) (q15 ◇ q12) q15 q15).symm)).trans (apc7 q15 q15 q12)
  exact (apc8 ((x ◇ y) ◇ x) (x ◇ y) x ((x ◇ y) ◇ x)).trans ((apc8 ((x ◇ y) ◇ x) ((z ◇ w) ◇ w) y ((x ◇ y) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47397_to_62044 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47397_to_62044
