-- Equation45610 → Equation52939
-- Recorded verdict: true
-- Premise: x * y = z * (((x * w) * w) * z)
-- Conclusion: x * x = (((x * x) * y) * y) * y
-- Original submission SHA-256: 0bc20134b0cd55e41e202079fcc5e4b4782730441539168660cf465f74a39509
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((x ◇ w) ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (((x ◇ x) ◇ y) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), (((q5 ◇ q4) ◇ q4) ◇ (q3 ◇ q3)) = (q5 ◇ q5):=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => ((q5 ◇ q4) ◇ q4) ◇ t) (apc1 q3 ((q5 ◇ q4) ◇ q4) q3)).symm).trans ((h q5 q6 ((q5 ◇ q4) ◇ q4) q4).symm)).trans (apc0 q5 q6 (q5 ◇ q6) (q5 ◇ q6))
  have apc3 : forall (q7 q8 q9 q10 q11:G), (((q8 ◇ q7) ◇ q7) ◇ q9) = (q10 ◇ q10):=by
    intro q7 q8 q9 q10 q11
    exact (((apc0 q10 (((q8 ◇ q8) ◇ (q11 ◇ q11)) ◇ q10) (q10 ◇ (((q8 ◇ q8) ◇ (q11 ◇ q11)) ◇ q10)) (q10 ◇ (((q8 ◇ q8) ◇ (q11 ◇ q11)) ◇ q10))).symm).trans (((congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ q10) (congrArg (fun t => t ◇ (q11 ◇ q11)) (apc2 q11 q7 q8 q11)))).symm).trans ((h ((q8 ◇ q7) ◇ q7) q9 q10 (q11 ◇ q11)).symm))).symm
  have apc9 : forall (q12 q13 q14 q15 q16 q17:G), ((((q13 ◇ q12) ◇ q12) ◇ ((q13 ◇ q12) ◇ q12)) ◇ (q13 ◇ q13)) = (q14 ◇ q14):=by
    intro q12 q13 q14 q15 q16 q17
    exact (((congrArg (fun t => (((q13 ◇ q12) ◇ q12) ◇ ((q14 ◇ q15) ◇ q15)) ◇ t) (apc0 q13 q16 (q13 ◇ q16) (q13 ◇ q16))).trans (congrArg (fun t => t ◇ (q13 ◇ q13)) (apc0 ((q13 ◇ q12) ◇ q12) ((q14 ◇ q15) ◇ q15) (((q13 ◇ q12) ◇ q12) ◇ ((q14 ◇ q15) ◇ q15)) (((q13 ◇ q12) ◇ q12) ◇ ((q14 ◇ q15) ◇ q15))))).symm).trans ((((congrArg (fun t => (((q13 ◇ q12) ◇ q12) ◇ ((q14 ◇ q15) ◇ q15)) ◇ t) ((h q13 q16 ((q14 ◇ q15) ◇ q15) q12).symm)).symm).trans ((h q14 q17 (((q13 ◇ q12) ◇ q12) ◇ ((q14 ◇ q15) ◇ q15)) q15).symm)).trans (apc0 q14 q17 (q14 ◇ q17) (q14 ◇ q17)))
  have apc10 : forall (q18 q19 q20 q21 q22:G), ((((q19 ◇ q18) ◇ q18) ◇ q20) ◇ (q21 ◇ q21)) = (q22 ◇ q22):=by
    intro q18 q19 q20 q21 q22
    exact ((congrArg (fun t => t ◇ (q21 ◇ q21)) ((apc3 q18 q19 q20 ((q21 ◇ q18) ◇ q18) q18).symm)).symm).trans (apc9 q18 q21 q22 q18 q18 q18)
  have apc12 : forall (q23 q24 q25 q26:G), ((q25 ◇ q23) ◇ q24) = (q26 ◇ q26):=by
    intro q23 q24 q25 q26
    exact (h (q25 ◇ q23) q24 (((q25 ◇ q23) ◇ q23) ◇ q23) q23).trans (apc10 q23 q25 q23 (((q25 ◇ q23) ◇ q23) ◇ q23) q26)
  exact ((apc12 x (x ◇ x) x x).symm).trans ((apc12 y y ((x ◇ x) ◇ y) (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45610_to_52939 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45610_to_52939
