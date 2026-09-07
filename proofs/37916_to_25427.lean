-- Equation37916 → Equation25427
-- Recorded verdict: true
-- Premise: x = ((y * (z * (w * y))) * z) * x
-- Conclusion: x = (y * (z * (x * w))) * (y * x)
-- Original submission SHA-256: 907f4b67a4becdfd4f01e695f51401934fd2249513078e4e6b2d45a1bfd41e4f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ (w ◇ y))) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ (q2 ◇ q1)) ◇ q2) ◇ q0) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q2) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q2 ◇ t) ((h q1 q0 q0 q0).symm))))).symm).trans ((h q0 q1 q2 ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (((q6 ◇ q6) ◇ ((q3 ◇ (q4 ◇ q3)) ◇ q4)) ◇ q5) = q5:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ ((q3 ◇ (q4 ◇ q3)) ◇ q4)) (congrArg (fun t => q6 ◇ t) (apc0 q6 q3 q4)))).symm).trans (apc0 q5 q6 ((q3 ◇ (q4 ◇ q3)) ◇ q4))
  have apc5 : forall (q7 q8 q9 q10:G), ((q7 ◇ ((q9 ◇ (q8 ◇ q8)) ◇ q7)) ◇ q10) = q10:=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ q10) (apc1 q7 (q9 ◇ (q8 ◇ q8)) (q7 ◇ ((q9 ◇ (q8 ◇ q8)) ◇ q7)) q8)).symm).trans ((h q10 (q8 ◇ q8) (q7 ◇ ((q9 ◇ (q8 ◇ q8)) ◇ q7)) q9).symm)
  have apc6 : forall (q11 q12 q13:G), ((q12 ◇ (q11 ◇ q11)) ◇ q13) = q13:=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ q13) (apc5 q11 q11 q12 (q12 ◇ (q11 ◇ q11)))).symm).trans (apc0 q13 q11 (q12 ◇ (q11 ◇ q11)))
  have apc11 : forall (q14 q15:G), (q15 ◇ q14) = q14:=by
    intro q14 q15
    exact ((congrArg (fun t => t ◇ q14) (apc6 q15 q15 q15)).symm).trans (apc0 q14 q15 q15)
  exact ((apc11 x y).symm).trans ((apc11 (y ◇ x) (y ◇ (z ◇ (x ◇ w)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_37916_to_25427 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_37916_to_25427
