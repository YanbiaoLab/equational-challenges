-- Equation27603 → Equation53891
-- Recorded verdict: true
-- Premise: x = ((x * (y * y)) * y) * (z * y)
-- Conclusion: x * (x * y) = x * (z * (w * x))
-- Original submission SHA-256: 74a5c334825069fe2240c0f412389dbc943cc16916bf8c7402694b7972c9f468
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ (y ◇ y)) ◇ y) ◇ (z ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = x ◇ (z ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ (q1 ◇ q1)) ◇ q1) = ((q0 ◇ q1) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ (q2 ◇ q1)) (congrArg (fun t => t ◇ q1) ((h q0 q1 q1).symm))).symm).trans ((h ((q0 ◇ (q1 ◇ q1)) ◇ q1) q1 q2).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q2 ◇ q1)) = ((q0 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q1 q0)
  have apc2 : forall (q0 q1 q2:G), ((q0 ◇ (q1 ◇ q1)) ◇ q1) = ((q0 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (apc0 q0 q1 q2).trans (apc1 q0 q1 q2)
  have apc3 : forall (q3 q4 q5:G), ((q4 ◇ q5) ◇ ((q3 ◇ q5) ◇ (q3 ◇ q5))) = ((q4 ◇ q5) ◇ (q4 ◇ q5)):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => (q4 ◇ q5) ◇ t) (apc2 q3 q5 q3)).symm).trans (apc1 q4 q5 (q3 ◇ (q5 ◇ q5)))
  have apc5 : forall (q6 q7 q8:G), ((q7 ◇ q8) ◇ (q7 ◇ q8)) = ((q7 ◇ q8) ◇ q6):=by
    intro q6 q7 q8
    exact (((congrArg (fun t => (q7 ◇ q8) ◇ t) ((h q6 q8 (q6 ◇ (q8 ◇ q8))).symm)).symm).trans (apc3 (q6 ◇ (q8 ◇ q8)) q7 q8)).symm
  have apc7 : forall (q9 q10 q11 q12:G), ((q11 ◇ q12) ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))) = ((q11 ◇ q12) ◇ (q11 ◇ q12)):=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => (q11 ◇ q12) ◇ t) ((apc5 q12 q9 q10).symm)).symm).trans (apc1 q11 q12 (q9 ◇ q10))
  have apc10 : forall (q0 q13 q14 q2:G), (((q14 ◇ q0) ◇ (q14 ◇ q0)) ◇ (q2 ◇ ((q0 ◇ q13) ◇ (q0 ◇ q13)))) = q14:=by
    intro q0 q13 q14 q2
    exact ((((congrArg (fun t => t ◇ (q2 ◇ ((q0 ◇ (q13 ◇ q13)) ◇ q13))) (congrArg (fun t => (q14 ◇ q0) ◇ t) (apc2 q0 q13 ((q0 ◇ (q13 ◇ q13)) ◇ q13)))).trans (congrArg (fun t => ((q14 ◇ q0) ◇ ((q0 ◇ q13) ◇ (q0 ◇ q13))) ◇ t) (congrArg (fun t => q2 ◇ t) (apc2 q0 q13 ((q0 ◇ (q13 ◇ q13)) ◇ q13))))).trans (congrArg (fun t => t ◇ (q2 ◇ ((q0 ◇ q13) ◇ (q0 ◇ q13)))) (apc7 q0 q13 q14 q0))).symm).trans (((congrArg (fun t => t ◇ (q2 ◇ ((q0 ◇ (q13 ◇ q13)) ◇ q13))) (congrArg (fun t => t ◇ ((q0 ◇ (q13 ◇ q13)) ◇ q13)) (congrArg (fun t => q14 ◇ t) ((h q0 q13 (q0 ◇ (q13 ◇ q13))).symm)))).symm).trans ((h q14 ((q0 ◇ (q13 ◇ q13)) ◇ q13) q2).symm))
  have apc11 : forall (q15 q16 q17 q18 q19:G), (q15 ◇ q16) = (q15 ◇ q15):=by
    intro q15 q16 q17 q18 q19
    exact (((congrArg (fun t => q15 ◇ t) (apc10 q17 q18 q15 q19)).symm).trans ((((congrArg (fun t => t ◇ (((q15 ◇ q17) ◇ (q15 ◇ q17)) ◇ (q19 ◇ ((q17 ◇ q18) ◇ (q17 ◇ q18))))) (apc10 q17 q18 q15 q19)).symm).trans (apc5 q16 ((q15 ◇ q17) ◇ (q15 ◇ q17)) (q19 ◇ ((q17 ◇ q18) ◇ (q17 ◇ q18))))).trans (congrArg (fun t => t ◇ q16) (apc10 q17 q18 q15 q19)))).symm
  exact (apc11 x (x ◇ y) (x ◇ (x ◇ y)) (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).trans ((apc11 x (z ◇ (w ◇ x)) (x ◇ (x ◇ y)) (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27603_to_53891 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27603_to_53891
