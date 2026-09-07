-- Equation19757 → Equation4604
-- Recorded verdict: true
-- Premise: x = (x ◇ y) ◇ ((z ◇ (y ◇ z)) ◇ z)
-- Conclusion: (x ◇ x) ◇ y = (x ◇ z) ◇ w
-- Original submission SHA-256: eb4a2aaf82536faf89ae037b30e1bc30fb650a0d9650d7f2dee5f38877ef5f6d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((z ◇ (y ◇ z)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (x ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc2 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q3 ◇ (((q2 ◇ (q1 ◇ q2)) ◇ q2) ◇ q3)) ◇ q3)) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q3 ◇ (((q2 ◇ (q1 ◇ q2)) ◇ q2) ◇ q3)) ◇ q3)) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q1) ((q2 ◇ (q1 ◇ q2)) ◇ q2) q3).symm)
  have apc3 : forall (q4 q5 q6:G), ((q6 ◇ ((q5 ◇ (q4 ◇ q5)) ◇ q5)) ◇ q4) = q6:=by
    intro q4 q5 q6
    exact ((apc2 (q6 ◇ ((q5 ◇ (q4 ◇ q5)) ◇ q5)) q4 q5 q4).symm).trans ((h q6 ((q5 ◇ (q4 ◇ q5)) ◇ q5) q4).symm)
  have apc4 : forall (q7 q8:G), ((q8 ◇ q7) ◇ (q7 ◇ (q7 ◇ q7))) = q8:=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ (q7 ◇ q7))) (congrArg (fun t => q8 ◇ t) (apc3 q7 q7 q7))).symm).trans (apc3 (q7 ◇ (q7 ◇ q7)) q7 q8)
  have apc5 : forall (q0 q1 q9:G), ((q9 ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) ◇ (q0 ◇ (q0 ◇ q1))) = q9:=by
    intro q0 q1 q9
    exact ((congrArg (fun t => (q9 ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) ◇ t) (congrArg (fun t => t ◇ (q0 ◇ q1)) ((h q0 q1 (q0 ◇ q1)).symm))).symm).trans ((h q9 ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1))) (q0 ◇ q1)).symm)
  have apc6 : forall (q10 q11:G), ((q10 ◇ (q11 ◇ (q11 ◇ q11))) ◇ q11) = q10:=by
    intro q10 q11
    exact ((congrArg (fun t => (q10 ◇ (q11 ◇ (q11 ◇ q11))) ◇ t) (apc3 q11 q11 q11)).symm).trans ((h q10 (q11 ◇ (q11 ◇ q11)) q11).symm)
  have apc7 : forall (q12 q13:G), ((q13 ◇ (q12 ◇ q12)) ◇ (q12 ◇ (q12 ◇ q12))) = q13:=by
    intro q12 q13
    exact ((congrArg (fun t => (q13 ◇ (q12 ◇ q12)) ◇ t) (apc5 q12 q12 (q12 ◇ (q12 ◇ q12)))).symm).trans ((h q13 (q12 ◇ q12) (q12 ◇ (q12 ◇ q12))).symm)
  have apc8 : forall (q14 q15:G), (q14 ◇ (q15 ◇ q15)) = (q14 ◇ q15):=by
    intro q14 q15
    exact (((congrArg (fun t => t ◇ q15) (apc7 q15 q14)).symm).trans (apc6 (q14 ◇ (q15 ◇ q15)) q15)).symm
  have apc10 : forall (q7 q8 q14 q15:G), ((q8 ◇ q7) ◇ q7) = q8:=by
    intro q7 q8 q14 q15
    exact (((congrArg (fun t => (q8 ◇ q7) ◇ t) (apc8 q7 q7)).trans (apc8 (q8 ◇ q7) q7)).symm).trans (apc4 q7 q8)
  have apc11 : forall (q16 q17 q18:G), (q16 ◇ ((q18 ◇ (q17 ◇ q18)) ◇ q18)) = (q16 ◇ q17):=by
    intro q16 q17 q18
    exact ((congrArg (fun t => t ◇ ((q18 ◇ (q17 ◇ q18)) ◇ q18)) (apc10 q17 q16 q16 q16)).symm).trans ((h (q16 ◇ q17) q17 q18).symm)
  have apc19 : forall (q19 q20 q21:G), (q20 ◇ ((q21 ◇ q19) ◇ q21)) = (q20 ◇ (q19 ◇ q21)):=by
    intro q19 q20 q21
    exact ((congrArg (fun t => q20 ◇ t) (congrArg (fun t => t ◇ q21) (congrArg (fun t => q21 ◇ t) (apc10 q21 q19 q19 q19)))).symm).trans (apc11 q20 (q19 ◇ q21) q21)
  have apc20 : forall (q22 q23 q24:G), ((q23 ◇ (q24 ◇ q22)) ◇ q22) = q23:=by
    intro q22 q23 q24
    exact (((apc19 (q22 ◇ q24) (q23 ◇ (q24 ◇ q22)) q24).trans (congrArg (fun t => (q23 ◇ (q24 ◇ q22)) ◇ t) (apc10 q24 q22 ((q22 ◇ q24) ◇ q24) ((q22 ◇ q24) ◇ q24)))).symm).trans (((congrArg (fun t => (q23 ◇ (q24 ◇ q22)) ◇ t) (congrArg (fun t => t ◇ q24) (apc19 q22 q24 q24))).symm).trans ((h q23 (q24 ◇ q22) q24).symm))
  have apc22 : forall (q25 q26 q27:G), ((q27 ◇ q25) ◇ q26) = q27:=by
    intro q25 q26 q27
    exact ((congrArg (fun t => t ◇ q26) (congrArg (fun t => q27 ◇ t) (apc10 q26 q25 q25 q25))).symm).trans (apc20 q26 q27 (q25 ◇ q26))
  exact (apc22 x y x).trans ((apc22 z w x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19757_to_4604 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19757_to_4604
