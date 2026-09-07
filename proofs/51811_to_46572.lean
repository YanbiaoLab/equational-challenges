-- Equation51811 → Equation46572
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * (w * x)) * z
-- Conclusion: x * y = (z * y) * (w * (u * v))
-- Original submission SHA-256: 82c411af3d6bd31a1879f32215e142fe33d7f77dbe4dc1dc53715149e8154d28
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ (w ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (z ◇ y) ◇ (w ◇ (u ◇ v))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q1 ◇ q2) ◇ ((q3 ◇ q4) ◇ q2)) = (q4 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ ((q3 ◇ q4) ◇ q2)) ((h q1 q2 (q3 ◇ q4) q0).symm)).symm).trans ((h q4 (q0 ◇ q1) ((q3 ◇ q4) ◇ q2) q3).symm)
  have apc1 : forall (q5 q6 q7 q8:G), ((q6 ◇ (q5 ◇ q8)) ◇ q8) = (q7 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ q8) (apc0 q5 q8 q7 q5 q6)).symm).trans ((h q7 q7 q8 (q5 ◇ q6)).symm)
  have apc2 : forall (q9 q10 q11 q12:G), ((q9 ◇ q10) ◇ q12) = (q11 ◇ q11):=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q12) ((h q9 q10 (q9 ◇ q12) q9).symm)).symm).trans (apc1 q9 (((q9 ◇ q12) ◇ q10) ◇ (q9 ◇ q9)) q11 q12)
  have apc3 : forall (q13 q14 q15 q16:G), ((q13 ◇ q13) ◇ q16) = (q14 ◇ q15):=by
    intro q13 q14 q15 q16
    exact ((congrArg (fun t => t ◇ q16) (apc2 q16 q15 q13 (q13 ◇ q14))).symm).trans ((h q14 q15 q16 q13).symm)
  exact ((apc3 (x ◇ y) x y ((z ◇ y) ◇ (w ◇ (u ◇ v)))).symm).trans (apc3 (x ◇ y) (z ◇ y) (w ◇ (u ◇ v)) ((z ◇ y) ◇ (w ◇ (u ◇ v))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51811_to_46572 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51811_to_46572
