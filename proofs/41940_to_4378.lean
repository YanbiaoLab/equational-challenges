-- Equation41940 → Equation4378
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (y ◇ (z ◇ (x ◇ x)))
-- Conclusion: x ◇ (y ◇ z) = w ◇ (u ◇ z)
-- Original submission SHA-256: 841897a3d7b62ed3d04504f45afda9b2db2268f145986ad5897f618d1e2f4ac3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ (z ◇ (x ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = w ◇ (u ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((congrArg (fun t => q1 ◇ t) ((h q0 q1 (q0 ◇ q0)).symm)).symm).trans ((h (q0 ◇ q0) q1 q1).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ (q3 ◇ ((q2 ◇ q2) ◇ q2))) = (q2 ◇ q3):=by
    intro q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q3 ◇ t) (apc0 q2 q2))).symm).trans ((h q2 q3 q2).symm)
  have apc2 : forall (q4 q5:G), ((q4 ◇ q4) ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((apc1 (q4 ◇ q4) q5).symm).trans ((h q4 q5 ((q4 ◇ q4) ◇ (q4 ◇ q4))).symm)
  have apc3 : forall (q0 q1 q4 q5:G), (q1 ◇ (q0 ◇ q1)) = (q0 ◇ q1):=by
    intro q0 q1 q4 q5
    exact (apc0 q0 q1).trans (apc2 q0 q1)
  have apc4 : forall (q6 q7:G), (q7 ◇ (q6 ◇ (q7 ◇ q7))) = (q6 ◇ (q7 ◇ q7)):=by
    intro q6 q7
    exact (((apc3 q6 (q7 ◇ q7) q6 q6).symm).trans (apc2 q7 (q6 ◇ (q7 ◇ q7)))).symm
  have apc6 : forall (q8 q9:G), (q9 ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q8 q9
    exact ((apc4 q9 q8).symm).trans (((congrArg (fun t => q8 ◇ t) (apc4 q9 q8)).symm).trans ((h q8 q8 q9).symm))
  have apc7 : forall (q10 q11:G), (q10 ◇ q11) = (q10 ◇ q10):=by
    intro q10 q11
    exact (((((congrArg (fun t => q11 ◇ t) (apc2 q10 (q10 ◇ q10))).trans (congrArg (fun t => q11 ◇ t) (apc3 q10 q10 (q10 ◇ (q10 ◇ q10)) (q10 ◇ (q10 ◇ q10))))).trans (apc6 q10 q11)).symm).trans (((congrArg (fun t => q11 ◇ t) (apc6 (q10 ◇ q10) q11)).symm).trans ((h q10 q11 (q10 ◇ q10)).symm))).symm
  have apc8 : forall (q0 q1 q4 q5 q10 q11:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q4 q5 q10 q11
    exact (((congrArg (fun t => q1 ◇ t) (apc7 q0 q1)).trans (apc7 q1 (q0 ◇ q0))).symm).trans ((apc3 q0 q1 q4 q5).trans (apc7 q0 q1))
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc7 x (y ◇ z)
    _ = (w ◇ w):=apc8 w x u u u u
    _ = (w ◇ (u ◇ z)):=(apc7 w (u ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41940_to_4378 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41940_to_4378
