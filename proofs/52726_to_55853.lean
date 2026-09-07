-- Equation52726 → Equation55853
-- Recorded verdict: true
-- Premise: x * y = ((z * (z * x)) * w) * z
-- Conclusion: x * (y * x) = (z * x) * (w * w)
-- Original submission SHA-256: 71b3e44f1065cba420a6d039e3b4b6f47585ef427b726bd03cae572e9166fe7f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (z ◇ x)) ◇ w) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = (z ◇ x) ◇ (w ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q1) ◇ (q2 ◇ (q2 ◇ q0))) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q2 ◇ q0))) ((h q0 q1 q2 ((q2 ◇ (q2 ◇ q0)) ◇ q3)).symm)).symm).trans ((h q3 q4 (q2 ◇ (q2 ◇ q0)) q2).symm)
  have apc1 : forall (q5 q6 q7 q8 q9:G), ((q5 ◇ q6) ◇ q9) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q9) (apc0 q9 (q9 ◇ q7) q5 q5 q6)).symm).trans ((h q7 q8 q9 (q5 ◇ (q5 ◇ q9))).symm)
  have apc2 : forall (q10 q11 q12 q13 q14 q15:G), ((q12 ◇ q13) ◇ (q10 ◇ q11)) = (q14 ◇ q15):=by
    intro q10 q11 q12 q13 q14 q15
    exact ((congrArg (fun t => (q12 ◇ q13) ◇ t) (apc1 q10 q10 q10 q11 ((q10 ◇ q10) ◇ q12))).symm).trans (apc0 q12 q13 (q10 ◇ q10) q14 q15)
  have apc3 : forall (q10 q11 q12 q13 q14 q15:G), ((q14 ◇ q14) ◇ (q14 ◇ q14)) = ((q12 ◇ q13) ◇ (q10 ◇ q11)):=by
    intro q10 q11 q12 q13 q14 q15
    exact ((apc2 q10 q11 q12 q13 q14 q15).trans ((apc2 q14 q14 q14 q14 q14 q15).symm)).symm
  have apc4 : forall (q16 q17 q18:G), ((q16 ◇ q16) ◇ (q16 ◇ q16)) = (q17 ◇ q18):=by
    intro q16 q17 q18
    exact (apc3 q16 q16 q16 q16 q16 q16).trans (apc2 q16 q16 q16 q16 q17 q18)
  exact ((apc4 (x ◇ (y ◇ x)) x (y ◇ x)).symm).trans (apc4 (x ◇ (y ◇ x)) (z ◇ x) (w ◇ w))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52726_to_55853 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52726_to_55853
