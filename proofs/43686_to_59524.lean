-- Equation43686 → Equation59524
-- Recorded verdict: true
-- Premise: x * y = y * ((y * y) * (x * z))
-- Conclusion: (x * y) * y = z * ((y * z) * z)
-- Original submission SHA-256: 0609fce7b638cbf0547e384daba4b57418291b43ce768cd7a1317abe068dd850
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((y ◇ y) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = z ◇ ((y ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1) = (q1 ◇ (q0 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (((congrArg (fun t => q1 ◇ t) ((h q0 (q1 ◇ q1) q0).symm)).symm).trans ((h ((q1 ◇ q1) ◇ (q1 ◇ q1)) q1 (q0 ◇ q0)).symm)).symm
  have apc1 : forall (q2:G), (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2) = (q2 ◇ q2):=by
    intro q2
    exact (apc0 (q2 ◇ q2) q2).trans ((h q2 q2 q2).symm)
  have apc2 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q1 ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((apc1 q1).symm).trans (apc0 q0 q1)).symm
  have apc3 : forall (q3 q4:G), (q4 ◇ q4) = (q3 ◇ q4):=by
    intro q3 q4
    exact ((apc2 (q4 ◇ q4) q4).symm).trans (((congrArg (fun t => q4 ◇ t) (apc2 q3 (q4 ◇ q4))).symm).trans ((h q3 q4 ((q4 ◇ q4) ◇ (q4 ◇ q4))).symm))
  have apc4 : forall (q5 q6 q7:G), (q6 ◇ q7) = (q5 ◇ q7):=by
    intro q5 q6 q7
    exact (((apc3 q5 q7).symm).trans (apc3 q6 q7)).symm
  have apc6 : forall (q8 q9 q10:G), (q9 ◇ ((q8 ◇ q10) ◇ (q8 ◇ q10))) = (q8 ◇ q9):=by
    intro q8 q9 q10
    exact ((congrArg (fun t => q9 ◇ t) ((apc3 (q9 ◇ q9) (q8 ◇ q10)).symm)).symm).trans ((h q8 q9 q10).symm)
  have apc7 : forall (q11 q12 q13 q14:G), (q11 ◇ q13) = (q11 ◇ q12):=by
    intro q11 q12 q13 q14
    exact (((apc6 q11 q13 q14).symm).trans (apc4 q12 q13 ((q11 ◇ q14) ◇ (q11 ◇ q14)))).trans (apc6 q11 q12 q14)
  have apc8 : forall (q15 q16 q17:G), (q15 ◇ q16) = (q15 ◇ q15):=by
    intro q15 q16 q17
    exact (((apc6 q15 q15 q17).symm).trans ((((apc6 q15 ((q15 ◇ q17) ◇ (q15 ◇ q17)) q17).symm).trans (apc3 q16 ((q15 ◇ q17) ◇ (q15 ◇ q17)))).trans (apc6 q15 q16 q17))).symm
  have apc9 : forall (q18 q19 q20:G), (q20 ◇ q18) = (q19 ◇ q19):=by
    intro q18 q19 q20
    exact (((apc7 q20 q18 ((q20 ◇ q20) ◇ (q19 ◇ q18)) q18).symm).trans ((h q19 q20 q18).symm)).trans (apc8 q19 q20 (q19 ◇ q20))
  exact (apc9 y ((x ◇ y) ◇ y) (x ◇ y)).trans ((apc9 ((y ◇ z) ◇ z) ((x ◇ y) ◇ y) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43686_to_59524 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43686_to_59524
