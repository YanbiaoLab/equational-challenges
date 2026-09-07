-- Equation59877 → Equation60102
-- Recorded verdict: true
-- Premise: (x * y) * z = w * ((z * u) * x)
-- Conclusion: (x * x) * y = (z * y) * (w * y)
-- Original submission SHA-256: 8f7d66d529c24eed550b31f1040b6d3c059123c5a2e92771f85b5937c1b2b97e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = w ◇ ((z ◇ u) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (z ◇ y) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q1 ◇ q2) ◇ q3) = ((q1 ◇ q0) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((h q1 q0 q3 q0 q0).trans ((h q1 q2 q3 q0 q0).symm)).symm
  have apc1 : forall (x y z w u:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q4 q5 q6 q7 q8 q9:G), (((q4 ◇ q4) ◇ q5) ◇ q8) = ((q7 ◇ q6) ◇ q8):=by
    intro q4 q5 q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q8) (apc1 q4 q9 q5 ((q4 ◇ q9) ◇ q5) ((q4 ◇ q9) ◇ q5))).symm).trans (((congrArg (fun t => t ◇ q8) ((h q4 q9 q5 q7 q4).symm)).symm).trans (apc0 q6 q7 ((q5 ◇ q4) ◇ q4) q8))
  have apc4 : forall (q4 q6 q7 q8 q5 q9:G), ((q7 ◇ q6) ◇ q8) = ((q4 ◇ q4) ◇ q8):=by
    intro q4 q6 q7 q8 q5 q9
    exact ((apc2 q4 q5 q6 q7 q8 q9).symm).trans (apc2 q4 q5 q4 q4 q8 q9)
  have apc7 : forall (q10 q11 q12 q13:G), (q11 ◇ ((q13 ◇ q10) ◇ q12)) = ((q12 ◇ q12) ◇ q13):=by
    intro q10 q11 q12 q13
    exact (((apc1 q12 q10 q13 q10 q10).symm).trans (h q12 q10 q13 q11 q10)).symm
  have apc8 : forall (q14 q15 q16 q17:G), ((q15 ◇ q15) ◇ q16) = ((q15 ◇ q15) ◇ q14):=by
    intro q14 q15 q16 q17
    exact (((apc7 q14 q17 q15 q14).symm).trans (((congrArg (fun t => q17 ◇ t) (apc4 q14 q14 q16 q15 q14 q14)).symm).trans (apc7 q14 q17 q15 q16))).symm
  have apc9 : forall (q18 q19 q20 q21 q22:G), ((q21 ◇ q20) ◇ q22) = ((q19 ◇ q19) ◇ q18):=by
    intro q18 q19 q20 q21 q22
    exact (((apc8 q18 q19 q22 q18).symm).trans ((apc4 q19 q20 q21 q22 q18 q18).symm)).symm
  exact (apc9 ((z ◇ y) ◇ (w ◇ y)) ((x ◇ x) ◇ y) x x y).trans ((apc9 ((z ◇ y) ◇ (w ◇ y)) ((x ◇ x) ◇ y) y z (w ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59877_to_60102 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59877_to_60102
