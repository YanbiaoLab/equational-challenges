-- Equation22607 → Equation2300
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ x)) ◇ ((y ◇ z) ◇ z)
-- Conclusion: x = (y ◇ (x ◇ (y ◇ x))) ◇ x
-- Original submission SHA-256: c6ed3153ffeccf6e6c3071dcf0e3e490383ff3303e61ce2354fe0a1a67c14d3c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ x)) ◇ ((y ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ (y ◇ x))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (((q1 ◇ (q1 ◇ q0)) ◇ q2) ◇ q2)) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (((q1 ◇ (q1 ◇ q0)) ◇ q2) ◇ q2)) ((h q0 q1 (q1 ◇ q0)).symm)).symm).trans ((h (q1 ◇ q0) (q1 ◇ (q1 ◇ q0)) q2).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ (q4 ◇ ((q5 ◇ q3) ◇ q3))) = (q5 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ ((q5 ◇ q3) ◇ q3)) ((h q4 q5 q3).symm))).symm).trans (apc0 q4 q5 ((q5 ◇ q3) ◇ q3))
  have apc2 : forall (q6 q7:G), ((q6 ◇ (q6 ◇ q7)) ◇ q7) = (q7 ◇ (q6 ◇ q7)):=by
    intro q6 q7
    exact (((congrArg (fun t => q7 ◇ t) (apc0 q7 q6 q6)).symm).trans (apc1 q6 q7 (q6 ◇ (q6 ◇ q7)))).symm
  have apc3 : forall (q8 q9:G), (q9 ◇ (q9 ◇ (q9 ◇ q8))) = (q8 ◇ (q9 ◇ q8)):=by
    intro q8 q9
    exact (((apc2 q9 q8).symm).trans (((congrArg (fun t => (q9 ◇ (q9 ◇ q8)) ◇ t) ((h q8 q9 q8).symm)).symm).trans (apc1 q8 (q9 ◇ (q9 ◇ q8)) q9))).symm
  have apc4 : forall (q10 q11:G), (q10 ◇ ((q11 ◇ q10) ◇ q10)) = (q11 ◇ (q11 ◇ q10)):=by
    intro q10 q11
    exact ((apc3 q10 (q11 ◇ q10)).symm).trans (apc1 q10 (q11 ◇ q10) q11)
  have apc6 : forall (q12 q13:G), (q13 ◇ (q12 ◇ (q13 ◇ q12))) = q12:=by
    intro q12 q13
    exact ((congrArg (fun t => q13 ◇ t) (apc3 q12 q13)).symm).trans (((apc4 (q13 ◇ (q13 ◇ q12)) q13).symm).trans ((h q12 q13 (q13 ◇ (q13 ◇ q12))).symm))
  have apc7 : forall (q14:G), (q14 ◇ (q14 ◇ q14)) = q14:=by
    intro q14
    exact (((apc6 q14 q14).symm).trans (apc3 q14 q14)).symm
  have apc8 : forall (q15:G), (q15 ◇ q15) = q15:=by
    intro q15
    exact (((congrArg (fun t => t ◇ q15) (apc7 q15)).symm).trans (apc2 q15 q15)).trans (apc7 q15)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (x ◇ (y ◇ x))) ◇ x):=((congrArg (fun t => t ◇ x) (apc6 x y)).trans (apc8 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22607_to_2300 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22607_to_2300
