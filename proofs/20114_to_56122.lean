-- Equation20114 → Equation56122
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ ((x ◇ (x ◇ y)) ◇ y)
-- Conclusion: x ◇ (y ◇ z) = (x ◇ w) ◇ (y ◇ x)
-- Original submission SHA-256: c262ad3823b02286e1bce52549261eacb2681d5eddcfa0610287ade71e497d47
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ (x ◇ y)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ w) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) (congrArg (fun t => t ◇ q0) ((h q0 q0 (q0 ◇ q0)).symm))).symm).trans ((h (q0 ◇ (q0 ◇ q0)) q0 q1).symm)
  have apc1 : forall (q2 q3:G), (((q2 ◇ q2) ◇ q3) ◇ (q2 ◇ (q2 ◇ q2))) = q2:=by
    intro q2 q3
    exact ((congrArg (fun t => ((q2 ◇ q2) ◇ q3) ◇ t) (apc0 q2 (q2 ◇ (q2 ◇ q2)))).symm).trans ((h q2 (q2 ◇ q2) q3).symm)
  have apc2 : forall (q4 q5:G), (q4 ◇ (q5 ◇ (q5 ◇ q5))) = q5:=by
    intro q4 q5
    exact ((congrArg (fun t => t ◇ (q5 ◇ (q5 ◇ q5))) ((h q4 q5 q5).symm)).symm).trans (apc1 q5 ((q4 ◇ (q4 ◇ q5)) ◇ q5))
  have apc3 : forall (q6 q7:G), (q7 ◇ (q7 ◇ q7)) = (q6 ◇ (q7 ◇ q7)):=by
    intro q6 q7
    exact (((congrArg (fun t => t ◇ (q7 ◇ q7)) (apc2 q7 q6)).symm).trans (apc0 q7 (q6 ◇ (q6 ◇ q6)))).symm
  have apc5 : forall (q8 q9 q10:G), (q9 ◇ (q10 ◇ q10)) = (q8 ◇ (q10 ◇ q10)):=by
    intro q8 q9 q10
    exact (((apc3 q8 q10).symm).trans (apc3 q9 q10)).symm
  have apc6 : forall (q11 q12 q13:G), ((q11 ◇ (q12 ◇ q12)) ◇ (q13 ◇ q13)) = (q13 ◇ (q13 ◇ q13)):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ (q13 ◇ q13)) (apc5 q11 q13 q12)).symm).trans (apc0 q13 (q12 ◇ q12))
  have apc9 : forall (q14 q15 q16 q17:G), (q14 ◇ (q15 ◇ q15)) = q16:=by
    intro q14 q15 q16 q17
    exact ((((congrArg (fun t => ((q16 ◇ q16) ◇ q17) ◇ t) (congrArg (fun t => t ◇ (q16 ◇ q16)) (apc2 (q14 ◇ (q15 ◇ q15)) q16))).trans (apc2 ((q16 ◇ q16) ◇ q17) q16)).symm).trans (((congrArg (fun t => ((q16 ◇ q16) ◇ q17) ◇ t) (congrArg (fun t => t ◇ (q16 ◇ q16)) (congrArg (fun t => (q14 ◇ (q15 ◇ q15)) ◇ t) (apc6 q14 q15 q16)))).symm).trans ((h (q14 ◇ (q15 ◇ q15)) (q16 ◇ q16) q17).symm))).symm
  exact ((apc9 ((x ◇ w) ◇ (y ◇ x)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).symm).trans (apc9 ((x ◇ w) ◇ (y ◇ x)) (x ◇ (y ◇ z)) ((x ◇ w) ◇ (y ◇ x)) (x ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20114_to_56122 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20114_to_56122
