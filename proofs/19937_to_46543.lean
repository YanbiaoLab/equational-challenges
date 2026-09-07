-- Equation19937 → Equation46543
-- Recorded verdict: true
-- Premise: x = (y * x) * ((z * (w * y)) * x)
-- Conclusion: x * y = (z * y) * (z * (w * y))
-- Original submission SHA-256: 47385e8fd501003f10570dd4151a448abbc6ffb582e63fec820d16bae2cc1cfa
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((z ◇ (w ◇ y)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ (z ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) (congrArg (fun t => t ◇ q0) ((h q1 q0 q0 q0).symm))).symm).trans ((h q0 q1 (q0 ◇ q1) (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ q2) = (q2 ◇ q2):=by
    intro q2 q3
    exact (((congrArg (fun t => q2 ◇ t) (apc0 q2 q3)).symm).trans (((congrArg (fun t => t ◇ ((q3 ◇ q2) ◇ (q3 ◇ q2))) (apc0 q2 q3)).symm).trans (apc0 (q3 ◇ q2) (q3 ◇ q2)))).symm
  have apc2 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact (((congrArg (fun t => t ◇ (q1 ◇ q0)) (apc1 q0 q1)).trans (congrArg (fun t => (q0 ◇ q0) ◇ t) (apc1 q0 q1))).symm).trans (apc0 q0 q1)
  have apc3 : forall (q4 q5 q6:G), ((q4 ◇ q5) ◇ (q4 ◇ q5)) = (q6 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6
    exact ((apc1 (q4 ◇ q5) (q5 ◇ (q6 ◇ (q4 ◇ q5)))).symm).trans (((congrArg (fun t => (q5 ◇ (q6 ◇ (q4 ◇ q5))) ◇ t) (apc0 (q4 ◇ q5) q6)).symm).trans ((h (q6 ◇ (q4 ◇ q5)) q5 q6 q4).symm))
  have apc4 : forall (q7 q8:G), (q7 ◇ (q8 ◇ q8)) = q8:=by
    intro q7 q8
    exact ((apc3 q8 q8 q7).symm).trans (apc2 q8 q7)
  have apc5 : forall (q9 q10 q11 q12:G), (q12 ◇ (q10 ◇ q11)) = (q9 ◇ (q10 ◇ q11)):=by
    intro q9 q10 q11 q12
    exact (((apc3 q10 q11 q9).symm).trans (apc3 q10 q11 q12)).symm
  have apc6 : forall (q13 q14 q15 q16:G), (q13 ◇ (q14 ◇ q15)) = q15:=by
    intro q13 q14 q15 q16
    exact (((apc4 q16 q15).symm).trans (((congrArg (fun t => q16 ◇ t) (apc1 q15 q14)).symm).trans (apc5 q13 q14 q15 q16))).symm
  exact (calc
    (x ◇ y) = (y ◇ y):=apc1 y x
    _ = (w ◇ y):=(apc1 y w).symm
    _ = ((z ◇ y) ◇ (z ◇ (w ◇ y))):=(apc6 (z ◇ y) z (w ◇ y) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19937_to_46543 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19937_to_46543
