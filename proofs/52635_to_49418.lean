-- Equation52635 → Equation49418
-- Recorded verdict: true
-- Premise: x * y = ((z * (y * x)) * x) * x
-- Conclusion: x * y = ((z * w) * u) * (v * w)
-- Original submission SHA-256: 5b984c5e898925611bc247bb7691a36be1045f681b1829ce77868655df78ffdf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (y ◇ x)) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ u) ◇ (v ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (q0 q1 q2:G), ((((q2 ◇ q1) ◇ q0) ◇ q1) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) ((h (q2 ◇ q1) q0 q0).symm))).symm).trans ((h q1 q2 ((q0 ◇ (q0 ◇ (q2 ◇ q1))) ◇ (q2 ◇ q1))).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc0 (q5 ◇ q4) q4 q3).symm).trans ((h q4 q5 (q3 ◇ q4)).symm)).symm
  have apc3 : forall (q6 q7:G), (q7 ◇ (q6 ◇ q7)) = ((q7 ◇ q6) ◇ q7):=by
    intro q6 q7
    exact (((congrArg (fun t => t ◇ q7) (apc0 q7 q7 q6)).symm).trans (apc0 q7 q7 (q6 ◇ q7))).symm
  have apc4 : forall (q8 q9 q10:G), ((q10 ◇ q8) ◇ q10) = (q10 ◇ q9):=by
    intro q8 q9 q10
    exact ((apc3 q8 q10).symm).trans (apc1 q9 q10 (q8 ◇ q10))
  have apc6 : forall (q11 q12 q13 q14:G), ((q14 ◇ q11) ◇ q13) = (q14 ◇ q12):=by
    intro q11 q12 q13 q14
    exact (((apc4 q11 q12 q14).symm).trans (apc1 q13 (q14 ◇ q11) q14)).symm
  have apc9 : forall (q15 q16 q17 q18:G), ((q18 ◇ q15) ◇ q16) = (q16 ◇ q17):=by
    intro q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ q16) (apc6 (q17 ◇ q16) q15 q16 q18)).symm).trans ((h q16 q17 q18).symm)
  have apc10 : forall (q19 q20 q21 q22:G), (q22 ◇ q20) = (q21 ◇ q19):=by
    intro q19 q20 q21 q22
    exact (((apc9 q19 q21 q19 q22).symm).trans (apc6 q19 q20 q21 q22)).symm
  have apc12 : forall (q19 q20 q21 q22:G), (q21 ◇ q19) = (q20 ◇ q20):=by
    intro q19 q20 q21 q22
    exact ((apc10 q19 q20 q21 q22).symm).trans (apc10 q20 q20 q20 q22)
  exact (apc12 y (x ◇ y) x (x ◇ y)).trans ((apc12 (v ◇ w) (x ◇ y) ((z ◇ w) ◇ u) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52635_to_49418 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52635_to_49418
