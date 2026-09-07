-- Equation49054 → Equation58444
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * x) * (y * x)
-- Conclusion: (x * y) * x = y * (y * (x * z))
-- Original submission SHA-256: 299bff7d0e5596a2f7738a2dfb472051e6cc4d19c35f62ef0f2fa64fdb6f19b4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ x) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = y ◇ (y ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ (q2 ◇ (q1 ◇ q0))) = ((q1 ◇ q0) ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (congrArg (fun t => t ◇ (q1 ◇ q0)) ((h q0 q1 q0).symm))).symm).trans ((h (q1 ◇ q0) q2 ((q0 ◇ q0) ◇ q0)).symm)
  have apc1 : forall (x y z:G), (((z ◇ x) ◇ x) ◇ (y ◇ x)) = (((x ◇ x) ◇ x) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (q3 q4:G), (((q3 ◇ q3) ◇ q3) ◇ (q4 ◇ q3)) = (q3 ◇ q4):=by
    intro q3 q4
    exact ((apc1 q3 q4 q3).symm).trans ((h q3 q4 q3).symm)
  have apc3 : forall (q5 q6 q7:G), (((q6 ◇ q7) ◇ (q7 ◇ q6)) ◇ (q6 ◇ q7)) = ((q7 ◇ q6) ◇ ((q5 ◇ q6) ◇ q6)):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => ((q6 ◇ q7) ◇ (q7 ◇ q6)) ◇ t) (apc2 q6 q7)).symm).trans (((congrArg (fun t => ((q6 ◇ q7) ◇ (q7 ◇ q6)) ◇ t) (apc1 q6 q7 q5)).symm).trans (apc0 q6 q7 ((q5 ◇ q6) ◇ q6)))
  have apc5 : forall (q8 q9:G), ((q8 ◇ q8) ◇ (q9 ◇ (q8 ◇ q8))) = ((q8 ◇ q8) ◇ (q8 ◇ q8)):=by
    intro q8 q9
    exact (((apc0 q8 q8 (q8 ◇ q8)).symm).trans ((((congrArg (fun t => t ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) (apc0 q8 q8 (q8 ◇ q8))).symm).trans (apc3 q9 (q8 ◇ q8) (q8 ◇ q8))).trans (apc0 q8 q8 (q9 ◇ (q8 ◇ q8))))).symm
  have apc6 : forall (q10 q11 q12:G), (((q11 ◇ q11) ◇ ((q10 ◇ q11) ◇ q11)) ◇ (q12 ◇ (q11 ◇ q11))) = ((q11 ◇ q11) ◇ q12):=by
    intro q10 q11 q12
    exact ((congrArg (fun t => t ◇ (q12 ◇ (q11 ◇ q11))) (apc3 q10 q11 q11)).symm).trans ((h (q11 ◇ q11) q12 (q11 ◇ q11)).symm)
  have apc8 : forall (q13 q14 q15:G), (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ q14) = ((q13 ◇ q13) ◇ (q13 ◇ q13)):=by
    intro q13 q14 q15
    exact (((((congrArg (fun t => t ◇ (q14 ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13)))) (apc5 q13 q15)).trans (apc5 (q13 ◇ q13) q14)).trans (apc0 q13 q13 (q13 ◇ q13))).symm).trans (((congrArg (fun t => t ◇ (q14 ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13)))) (apc0 q13 q13 (q15 ◇ (q13 ◇ q13)))).symm).trans (apc6 q15 (q13 ◇ q13) q14))).symm
  have apc11 : forall (q16 q17 q18:G), ((q16 ◇ q16) ◇ (q16 ◇ q16)) = (q17 ◇ q18):=by
    intro q16 q17 q18
    exact (((congrArg (fun t => t ◇ (q18 ◇ q17)) (apc8 q16 q17 (((q16 ◇ q16) ◇ (q16 ◇ q16)) ◇ q17))).trans (apc8 q16 (q18 ◇ q17) (((q16 ◇ q16) ◇ (q16 ◇ q16)) ◇ (q18 ◇ q17)))).symm).trans (((congrArg (fun t => t ◇ (q18 ◇ q17)) (congrArg (fun t => t ◇ q17) (apc8 q16 q17 q16))).symm).trans ((h q17 q18 ((q16 ◇ q16) ◇ (q16 ◇ q16))).symm))
  exact ((apc11 ((x ◇ y) ◇ x) (x ◇ y) x).symm).trans (apc11 ((x ◇ y) ◇ x) y (y ◇ (x ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49054_to_58444 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49054_to_58444
