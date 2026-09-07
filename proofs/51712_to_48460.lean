-- Equation51712 → Equation48460
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (y * w)) * z
-- Conclusion: x * y = (z * (w * z)) * (x * u)
-- Original submission SHA-256: 2a7c82545a845698842f2b96e392a9671f295c3cd026e7e9dc5901b2e870cbd6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ (y ◇ w)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (w ◇ z)) ◇ (x ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q1 ◇ q2) ◇ ((q4 ◇ q3) ◇ q1)) = ((q2 ◇ q0) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ ((q4 ◇ q3) ◇ q1)) ((h q1 q2 (q4 ◇ q3) q0).symm)).symm).trans ((h (q2 ◇ q0) q4 ((q4 ◇ q3) ◇ q1) q3).symm)
  have apc2 : forall (q5 q6 q7 q8 q9:G), (((q9 ◇ q5) ◇ q7) ◇ q8) = (q9 ◇ (q7 ◇ q6)):=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q8) (apc0 q5 q8 q9 q6 q7)).symm).trans ((h q9 (q7 ◇ q6) q8 q8).symm)
  have apc4 : forall (q10 q11 q12 q13 q14:G), (q11 ◇ (q13 ◇ q10)) = ((q13 ◇ q12) ◇ q14):=by
    intro q10 q11 q12 q13 q14
    exact ((apc2 q10 q10 q13 ((q14 ◇ q10) ◇ (q11 ◇ q10)) q11).symm).trans (apc0 q12 (q11 ◇ q10) q13 q10 q14)
  have apc6 : forall (q15 q16 q17 q18 q19:G), ((q16 ◇ q15) ◇ q17) = (q18 ◇ q19):=by
    intro q15 q16 q17 q18 q19
    exact ((apc4 q15 (((q16 ◇ q15) ◇ q18) ◇ (q19 ◇ q15)) q15 q16 q17).symm).trans ((h q18 q19 (q16 ◇ q15) q15).symm)
  have apc8 : forall (q15 q18 q19 q16 q17:G), (q18 ◇ q19) = (q15 ◇ q15):=by
    intro q15 q18 q19 q16 q17
    exact ((apc6 q15 q16 q17 q18 q19).symm).trans (apc6 q15 q16 q17 q15 q15)
  exact (apc8 (x ◇ y) x y (x ◇ y) (x ◇ y)).trans ((apc8 (x ◇ y) (z ◇ (w ◇ z)) (x ◇ u) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51712_to_48460 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51712_to_48460
