-- Equation49281 → Equation61109
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * x) * (x * x)
-- Conclusion: (x * y) * x = (z * (x * z)) * y
-- Original submission SHA-256: 5b472cff4026376f2c627d117ae738376356a3aabe35270105cc478cbf1ad162
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ x) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ (x ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc1 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc2 : forall (q3 q4 q5 q6 q7:G), (((q6 ◇ q4) ◇ q5) ◇ q3) = (q5 ◇ q5):=by
    intro q3 q4 q5 q6 q7
    exact (((apc0 q3 ((q6 ◇ q4) ◇ q5) (q5 ◇ q5)).symm).trans ((h q5 q7 q6 q4).symm)).trans (apc1 q5 q7 (q5 ◇ q7) (q5 ◇ q7))
  have apc3 : forall (q8 q9 q10 q11:G), ((q10 ◇ q8) ◇ (q10 ◇ q8)) = (q9 ◇ q9):=by
    intro q8 q9 q10 q11
    exact ((apc2 q11 q8 (q10 ◇ q8) q10 (((q10 ◇ q8) ◇ (q10 ◇ q8)) ◇ q11)).symm).trans (((congrArg (fun t => t ◇ q11) (apc1 (q10 ◇ q8) q9 q11 q11)).symm).trans (apc2 q11 q8 q9 q10 q11))
  have apc6 : forall (q12 q13 q14 q15:G), ((q15 ◇ q13) ◇ q14) = (q12 ◇ q12):=by
    intro q12 q13 q14 q15
    exact (((apc3 (q15 ◇ q13) q12 (q15 ◇ q13) q12).symm).trans ((h (q15 ◇ q13) q14 q15 q13).symm)).symm
  exact (apc6 ((x ◇ y) ◇ x) y x x).trans ((apc6 ((x ◇ y) ◇ x) (x ◇ z) y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49281_to_61109 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49281_to_61109
