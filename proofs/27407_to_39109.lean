-- Equation27407 → Equation39109
-- Recorded verdict: true
-- Premise: x = ((y * z) * (w * y)) * (u * v)
-- Conclusion: x = (((y * x) * (x * x)) * z) * z
-- Original submission SHA-256: ab44fc816d00705193dec0e8f6df2c134beba5e1fccece62e5c56042b8b68e17
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = ((y ◇ z) ◇ (w ◇ y)) ◇ (u ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ (x ◇ x)) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5 q6:G), ((((q0 ◇ q1) ◇ q6) ◇ q2) ◇ (q3 ◇ q4)) = q5:=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q3 ◇ q4)) (congrArg (fun t => ((q0 ◇ q1) ◇ q6) ◇ t) ((h q2 q0 q0 q0 q0 q1).symm))).symm).trans ((h q5 (q0 ◇ q1) q6 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q3 q4).symm)
  have apc1 : forall (q7 q8 q9 q10 q11 q12:G), ((((q8 ◇ q9) ◇ q12) ◇ q10) ◇ q7) = q11:=by
    intro q7 q8 q9 q10 q11 q12
    exact ((congrArg (fun t => (((q8 ◇ q9) ◇ q12) ◇ q10) ◇ t) (apc0 q7 q7 q7 q7 q7 q7 q7)).symm).trans (apc0 q8 q9 q10 (((q7 ◇ q7) ◇ q7) ◇ q7) (q7 ◇ q7) q11 q12)
  have apc4 : forall (q13 q14 q15 q16:G), ((q13 ◇ q15) ◇ q14) = q16:=by
    intro q13 q14 q15 q16
    exact ((congrArg (fun t => t ◇ q14) (congrArg (fun t => t ◇ q15) (apc1 q13 q13 q13 q13 q13 q13))).symm).trans (apc1 q14 ((q13 ◇ q13) ◇ q13) q13 q15 q16 q13)
  exact ((apc4 x (x ◇ x) x x).symm).trans ((apc4 ((y ◇ x) ◇ (x ◇ x)) z z ((x ◇ x) ◇ (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27407_to_39109 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27407_to_39109
