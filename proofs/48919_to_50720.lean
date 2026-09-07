-- Equation48919 → Equation50720
-- Recorded verdict: true
-- Premise: x * y = ((y * x) * z) * (x * x)
-- Conclusion: x * y = (y * ((y * z) * z)) * z
-- Original submission SHA-256: 22aa5b8da7725a698f8d73a1d1ac4b81db3533543481c1d47470123290ac37ab
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ x) ◇ z) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ ((y ◇ z) ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q2 ◇ q2)) = (q2 ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) ((h q0 q1 q2).symm)).symm).trans ((h q2 (q1 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ (q5 ◇ (q4 ◇ q3))) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((apc0 (q4 ◇ q3) q5 q3).symm).trans ((h q3 q4 q5).symm)
  have apc2 : forall (q6 q7:G), (q7 ◇ (q7 ◇ q6)) = (q7 ◇ q7):=by
    intro q6 q7
    exact ((congrArg (fun t => q7 ◇ t) ((h q7 q6 q6).symm)).symm).trans (apc1 q7 q7 ((q6 ◇ q7) ◇ q6))
  have apc3 : forall (q8 q9:G), (q9 ◇ q9) = (q9 ◇ q8):=by
    intro q8 q9
    exact ((apc2 (q8 ◇ q9) q9).symm).trans (apc1 q9 q8 q9)
  have apc4 : forall (q10 q11:G), ((q11 ◇ q11) ◇ q10) = (q11 ◇ q11):=by
    intro q10 q11
    exact (((apc3 q10 (q11 ◇ q11)).symm).trans (apc0 q11 q11 q11)).trans (apc2 q11 q11)
  have apc5 : forall (q12 q13 q14:G), ((q14 ◇ q12) ◇ q13) = (q14 ◇ q14):=by
    intro q12 q13 q14
    exact ((congrArg (fun t => t ◇ q13) (apc3 q12 q14)).symm).trans (apc4 q13 q14)
  have apc6 : forall (q15 q16 q17:G), (q17 ◇ q16) = (q17 ◇ q15):=by
    intro q15 q16 q17
    exact (((apc3 q15 q17).symm).trans (apc3 q16 q17)).symm
  have apc7 : forall (q18 q19:G), (q19 ◇ q19) = (q18 ◇ q19):=by
    intro q18 q19
    exact ((apc5 q18 (q19 ◇ q18) q19).symm).trans (((apc5 q18 (q18 ◇ q18) (q19 ◇ q18)).symm).trans ((h q18 q19 q18).symm))
  have apc8 : forall (q20 q21 q22:G), (q22 ◇ q21) = (q20 ◇ q22):=by
    intro q20 q21 q22
    exact (((apc7 q20 q22).symm).trans (apc6 q21 q22 q22)).symm
  exact (apc8 z y x).trans (apc8 (y ◇ ((y ◇ z) ◇ z)) x z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48919_to_50720 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48919_to_50720
