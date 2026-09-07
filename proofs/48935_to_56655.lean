-- Equation48935 → Equation56655
-- Recorded verdict: true
-- Premise: x * y = ((y * x) * z) * (w * u)
-- Conclusion: x * (y * x) = (x * (y * y)) * y
-- Original submission SHA-256: 8518adffe9b3020276f4e8d23b6c7722892b37267262dde4d4e03cd20690bce7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((y ◇ x) ◇ z) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = (x ◇ (y ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ (q3 ◇ q2)) = (q4 ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) ((h q0 q1 q4 q0 q0).symm)).symm).trans ((h q4 (q1 ◇ q0) (q0 ◇ q0) q3 q2).symm)
  have apc4 : forall (q5 q6 q7 q8 q9:G), ((q5 ◇ (q8 ◇ q9)) ◇ (q7 ◇ q6)) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ (q7 ◇ q6)) (apc0 q9 q8 q5 q5 q5)).symm).trans ((h q8 q9 (q5 ◇ q5) q7 q6).symm)
  have apc5 : forall (x y z w u:G), (((y ◇ x) ◇ z) ◇ (w ◇ u)) = (((y ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z w u
    exact ((h x y z w u).symm).trans (h x y x x x)
  have apc6 : forall (q10 q11 q12 q13 q14:G), (q12 ◇ (q11 ◇ q10)) = (q10 ◇ q10):=by
    intro q10 q11 q12 q13 q14
    exact (((apc4 ((q11 ◇ q10) ◇ q10) q13 q14 q10 q10).symm).trans (((congrArg (fun t => t ◇ (q14 ◇ q13)) (apc5 q10 q11 q12 q10 q10)).symm).trans ((h q12 (q11 ◇ q10) (q10 ◇ q10) q14 q13).symm))).symm
  have apc7 : forall (q15 q16 q17 q18 q19 q20:G), ((q16 ◇ q15) ◇ q18) = (q17 ◇ q17):=by
    intro q15 q16 q17 q18 q19 q20
    exact (((apc6 q17 q19 ((q15 ◇ q15) ◇ q20) (((q15 ◇ q15) ◇ q20) ◇ (q19 ◇ q17)) (((q15 ◇ q15) ◇ q20) ◇ (q19 ◇ q17))).symm).trans (((congrArg (fun t => t ◇ (q19 ◇ q17)) (congrArg (fun t => t ◇ q20) (apc6 q15 q16 q18 q15 q15))).symm).trans ((h (q16 ◇ q15) q18 q20 q19 q17).symm))).symm
  have apc8 : forall (q21 q22 q23:G), ((q21 ◇ q21) ◇ q23) = (q22 ◇ q22):=by
    intro q21 q22 q23
    exact ((congrArg (fun t => t ◇ q23) (apc6 q21 q21 q21 q21 q21)).symm).trans (apc7 (q21 ◇ q21) q21 q22 q23 q21 q21)
  have apc9 : forall (q24 q25 q26 q27:G), ((q24 ◇ q24) ◇ q25) = (q26 ◇ q27):=by
    intro q24 q25 q26 q27
    exact (apc8 q24 ((q27 ◇ q26) ◇ q24) q25).trans ((h q26 q27 q24 (q27 ◇ q26) q24).symm)
  exact ((apc9 (x ◇ (y ◇ x)) ((x ◇ (y ◇ y)) ◇ y) x (y ◇ x)).symm).trans (apc9 (x ◇ (y ◇ x)) ((x ◇ (y ◇ y)) ◇ y) (x ◇ (y ◇ y)) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48935_to_56655 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48935_to_56655
