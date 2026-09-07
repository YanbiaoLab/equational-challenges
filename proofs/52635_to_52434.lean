-- Equation52635 → Equation52434
-- Recorded verdict: true
-- Premise: x * y = ((z * (y * x)) * x) * x
-- Conclusion: x * y = ((y * (x * z)) * y) * w
-- Original submission SHA-256: d7827697df653d77253ae89c988d9c8d92cf78fe01b5190c962af10d48ccdb67
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (y ◇ x)) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ (x ◇ z)) ◇ y) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((((q2 ◇ q1) ◇ q0) ◇ q1) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) ((h (q2 ◇ q1) q0 q0).symm))).symm).trans ((h q1 q2 ((q0 ◇ (q0 ◇ (q2 ◇ q1))) ◇ (q2 ◇ q1))).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact (((apc0 (q5 ◇ q4) q4 q3).symm).trans ((h q4 q5 (q3 ◇ q4)).symm)).symm
  have apc2 : forall (q6 q7 q8 q9:G), (((q9 ◇ (q8 ◇ q7)) ◇ q7) ◇ q6) = (q7 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((apc1 q6 ((q9 ◇ (q8 ◇ q7)) ◇ q7) q7).symm).trans ((h q7 q8 q9).symm)
  have apc5 : forall (q10 q11 q12 q13 q14:G), (((q14 ◇ (q13 ◇ q12)) ◇ q10) ◇ q11) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ q11) (apc1 q10 (q14 ◇ (q13 ◇ q12)) q12)).symm).trans (apc2 q11 q12 q13 q14)
  have apc6 : forall (q15 q16 q17 q18:G), (((q18 ◇ q17) ◇ q15) ◇ q16) = (q17 ◇ q18):=by
    intro q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ q16) (apc2 q17 (q18 ◇ q17) q15 q15)).symm).trans (apc2 q16 q17 q18 (q15 ◇ (q15 ◇ (q18 ◇ q17))))
  have apc13 : forall (q10 q11 q12 q13 q14 q15 q16 q17 q18:G), ((q13 ◇ q12) ◇ q14) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13 q14 q15 q16 q17 q18
    exact ((apc6 q10 q11 (q13 ◇ q12) q14).symm).trans (apc5 q10 q11 q12 q13 q14)
  have apc15 : forall (q6 q7 q8 q9:G), (q9 ◇ q6) = (q7 ◇ q8):=by
    intro q6 q7 q8 q9
    exact (((congrArg (fun t => t ◇ q7) (apc13 ((q9 ◇ q6) ◇ q7) ((q9 ◇ q6) ◇ q7) q6 q9 q7 ((q9 ◇ q6) ◇ q7) ((q9 ◇ q6) ◇ q7) ((q9 ◇ q6) ◇ q7) ((q9 ◇ q6) ◇ q7))).trans (apc13 ((q6 ◇ q9) ◇ q7) ((q6 ◇ q9) ◇ q7) q9 q6 q7 ((q6 ◇ q9) ◇ q7) ((q6 ◇ q9) ◇ q7) ((q6 ◇ q9) ◇ q7) ((q6 ◇ q9) ◇ q7))).symm).trans (((congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ q7) (apc1 q6 q9 (q8 ◇ q7)))).symm).trans ((h q7 q8 q9).symm))
  exact (apc15 y (x ◇ y) (((y ◇ (x ◇ z)) ◇ y) ◇ w) x).trans ((apc15 w (x ◇ y) (((y ◇ (x ◇ z)) ◇ y) ◇ w) ((y ◇ (x ◇ z)) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52635_to_52434 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52635_to_52434
