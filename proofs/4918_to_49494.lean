-- Equation4918 → Equation49494
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ (z ◇ (x ◇ x))))
-- Conclusion: x ◇ x = (y ◇ (x ◇ (z ◇ x))) ◇ x
-- Original submission SHA-256: 6f41f5f93b2e7a640832d544391c0b54d70d284a49ada70364e3391dc11d46e1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ (z ◇ (x ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (x ◇ (z ◇ x))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ ((q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ (q3 ◇ q0)))) = (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ t) (congrArg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ t) (congrArg (fun t => q3 ◇ t) ((h q0 (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) q1).symm))))).symm).trans ((h (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) q2 q3).symm)
  have apc3 : forall (q4 q5 q6 q7:G), (q6 ◇ (((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q5 ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q7 ◇ (q4 ◇ (q7 ◇ q7))))))) ◇ q7)) = ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q5 ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q7 ◇ (q4 ◇ (q7 ◇ q7))))))):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q5 ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q7 ◇ (q4 ◇ (q7 ◇ q7))))))) ◇ t) ((h q7 ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q5 ◇ ((q7 ◇ (q4 ◇ (q7 ◇ q7))) ◇ (q7 ◇ (q4 ◇ (q7 ◇ q7))))))) q4).symm))).symm).trans (apc2 (q7 ◇ (q4 ◇ (q7 ◇ q7))) q5 q6 q7)
  have apc4 : forall (q8 q9 q10 q11 q12:G), (q12 ◇ ((q10 ◇ (q10 ◇ (q11 ◇ (q10 ◇ q10)))) ◇ ((q10 ◇ (q8 ◇ (q10 ◇ q10))) ◇ ((q10 ◇ (q8 ◇ (q10 ◇ q10))) ◇ (q9 ◇ ((q10 ◇ (q8 ◇ (q10 ◇ q10))) ◇ (q10 ◇ (q8 ◇ (q10 ◇ q10))))))))) = (q10 ◇ (q10 ◇ (q11 ◇ (q10 ◇ q10)))):=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => q12 ◇ t) (congrArg (fun t => (q10 ◇ (q10 ◇ (q11 ◇ (q10 ◇ q10)))) ◇ t) (apc3 q8 q9 (q10 ◇ (q10 ◇ (q11 ◇ (q10 ◇ q10)))) q10))).symm).trans (apc2 q10 q11 q12 ((q10 ◇ (q8 ◇ (q10 ◇ q10))) ◇ ((q10 ◇ (q8 ◇ (q10 ◇ q10))) ◇ (q9 ◇ ((q10 ◇ (q8 ◇ (q10 ◇ q10))) ◇ (q10 ◇ (q8 ◇ (q10 ◇ q10))))))))
  have apc5 : forall (q13 q14 q15 q16:G), (q16 ◇ (q14 ◇ (q13 ◇ (q14 ◇ q14)))) = (q14 ◇ (q14 ◇ (q15 ◇ (q14 ◇ q14)))):=by
    intro q13 q14 q15 q16
    exact ((congrArg (fun t => q16 ◇ t) ((h (q14 ◇ (q13 ◇ (q14 ◇ q14))) (q14 ◇ (q14 ◇ (q15 ◇ (q14 ◇ q14)))) q13).symm)).symm).trans (apc4 q13 q13 q14 q15 q16)
  have apc6 : forall (q17 q18 q19 q20:G), (q20 ◇ (q18 ◇ (q19 ◇ (q17 ◇ (q19 ◇ q19))))) = q19:=by
    intro q17 q18 q19 q20
    exact ((congrArg (fun t => q20 ◇ t) ((apc5 q17 q19 q17 q18).symm)).symm).trans ((h q19 q20 q17).symm)
  have apc7 : forall (q21 q22:G), (q22 ◇ q22) = (q21 ◇ q22):=by
    intro q21 q22
    exact (((congrArg (fun t => q21 ◇ t) (apc6 (q22 ◇ q22) (q22 ◇ q22) q22 (q22 ◇ q22))).symm).trans ((h (q22 ◇ q22) q21 q22).symm)).symm
  exact (apc7 x x).trans (apc7 (y ◇ (x ◇ (z ◇ x))) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4918_to_49494 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4918_to_49494
