-- Equation7835 → Equation54832
-- Recorded verdict: true
-- Premise: x = y * (z * ((x * (x * y)) * x))
-- Conclusion: x * (x * y) = z * ((y * y) * y)
-- Original submission SHA-256: 1f1ce6f8a9d4cc6f6b63640c069cf88509e7c58cb7e57d998fc3ff71e60768e8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((x ◇ (x ◇ y)) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = z ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ q2)) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => q1 ◇ t) ((h q0 q2 (((q0 ◇ (q0 ◇ q2)) ◇ q0) ◇ (((q0 ◇ (q0 ◇ q2)) ◇ q0) ◇ q1))).symm)).symm).trans ((h ((q0 ◇ (q0 ◇ q2)) ◇ q0) q1 q2).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q0 q2)
  have apc2 : forall (q3 q4:G), (q4 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) = q3:=by
    intro q3 q4
    exact (((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ ((q3 ◇ (q3 ◇ q4)) ◇ q3)) (apc1 q3 (q3 ◇ (q3 ◇ q4)) ((q3 ◇ (q3 ◇ q4)) ◇ q3)))).trans (congrArg (fun t => q4 ◇ t) (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc1 q3 (q3 ◇ (q3 ◇ q4)) ((q3 ◇ (q3 ◇ q4)) ◇ q3))))).symm).trans (((congrArg (fun t => q4 ◇ t) (apc1 ((q3 ◇ (q3 ◇ q4)) ◇ q3) q3 q3)).symm).trans ((h q3 q4 q3).symm))
  have apc3 : forall (q5 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q6 ◇ (q5 ◇ q5)):=by
    intro q5 q6
    exact (((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q5 ◇ t) (apc2 q5 ((q5 ◇ q5) ◇ (q5 ◇ q5))))).symm).trans (((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5)))) (apc2 q5 ((q5 ◇ q5) ◇ (q5 ◇ q5))))).symm).trans (apc2 ((q5 ◇ q5) ◇ (q5 ◇ q5)) q6))).symm
  have apc5 : forall (q5 q6:G), (q6 ◇ (q5 ◇ q5)) = (q5 ◇ (q5 ◇ q5)):=by
    intro q5 q6
    exact ((apc3 q5 q6).symm).trans (apc3 q5 q5)
  have apc7 : forall (q7 q8 q9 q10:G), (q9 ◇ (q10 ◇ (q7 ◇ q8))) = q8:=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => q9 ◇ t) (congrArg (fun t => q10 ◇ t) (apc0 q8 q7 q9))).symm).trans ((h q8 q9 q10).symm)
  have apc8 : forall (q11 q12 q13 q14 q15:G), (q13 ◇ (q11 ◇ q12)) = (q12 ◇ (q12 ◇ q12)):=by
    intro q11 q12 q13 q14 q15
    exact ((((congrArg (fun t => q14 ◇ t) (apc1 q12 q15 (q15 ◇ q12))).trans (apc5 q12 q14)).symm).trans (((congrArg (fun t => q14 ◇ t) (congrArg (fun t => q15 ◇ t) (apc7 q11 q12 q11 q13))).symm).trans (apc7 q11 (q13 ◇ (q11 ◇ q12)) q14 q15))).symm
  exact (apc8 x y x (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).trans ((apc8 (y ◇ y) y z (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7835_to_54832 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_7835_to_54832
