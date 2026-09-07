-- Equation49057 → Equation50704
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * x) * (y * w)
-- Conclusion: x * y = (y * ((y * y) * y)) * y
-- Original submission SHA-256: d04d0980dac9026ff3c05d9ece10543ae5b25bfe17b5a7ad6eeafe0441e01597
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ x) ◇ (y ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ ((y ◇ y) ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q1) ◇ (q3 ◇ q2)) = ((q1 ◇ q0) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) ((h (q1 ◇ q0) q1 q0 q0).symm)).symm).trans ((h (q1 ◇ q0) q3 (q0 ◇ (q1 ◇ q0)) q2).symm)
  have apc1 : forall (q4 q5:G), ((q4 ◇ q4) ◇ q5) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((apc0 q4 q4 q4 q5).symm).trans ((h q4 q5 q4 q4).symm)
  have apc2 : forall (q6 q7:G), ((q6 ◇ (q6 ◇ q6)) ◇ q7) = (q6 ◇ q7):=by
    intro q6 q7
    exact (((congrArg (fun t => t ◇ q7) (apc1 q6 (q6 ◇ q6))).symm).trans (apc1 (q6 ◇ q6) q7)).trans (apc1 q6 q7)
  have apc5 : forall (x y z w:G), (((z ◇ x) ◇ x) ◇ (y ◇ w)) = (x ◇ (y ◇ x)):=by
    intro x y z w
    exact (((h x y z w).symm).trans (h x y x x)).trans ((congrArg (fun t => t ◇ (y ◇ x)) (apc1 x x)).trans (apc1 x (y ◇ x)))
  have apc6 : forall (q8 q9 q10:G), (((q9 ◇ q8) ◇ q8) ◇ q10) = (q8 ◇ q10):=by
    intro q8 q9 q10
    exact ((((congrArg (fun t => t ◇ q10) (apc5 q8 q8 q9 ((q9 ◇ q8) ◇ q8))).trans (apc2 q8 q10)).symm).trans (((congrArg (fun t => t ◇ q10) (congrArg (fun t => ((q9 ◇ q8) ◇ q8) ◇ t) (apc5 q8 (q9 ◇ q8) q9 q8))).symm).trans (apc2 ((q9 ◇ q8) ◇ q8) q10))).symm
  have apc8 : forall (q11 q12 q13 q14:G), ((q12 ◇ (q11 ◇ q12)) ◇ (q14 ◇ q13)) = (q12 ◇ q14):=by
    intro q11 q12 q13 q14
    exact (((congrArg (fun t => t ◇ (q14 ◇ q13)) (apc6 q12 q11 (q11 ◇ q12))).symm).trans (apc0 q12 (q11 ◇ q12) q13 q14)).trans (apc6 q12 q11 q14)
  have apc9 : forall (q15 q16 q17:G), ((q16 ◇ (q15 ◇ q16)) ◇ q17) = (q16 ◇ q17):=by
    intro q15 q16 q17
    exact ((((congrArg (fun t => t ◇ q17) (apc8 q15 q16 q16 q16)).trans (apc1 q16 q17)).symm).trans (((congrArg (fun t => t ◇ q17) (congrArg (fun t => (q16 ◇ (q15 ◇ q16)) ◇ t) (apc8 q15 q16 (q15 ◇ q16) q16))).symm).trans (apc2 (q16 ◇ (q15 ◇ q16)) q17))).symm
  have apc10 : forall (q18 q19 q20:G), ((q18 ◇ q19) ◇ q20) = (q19 ◇ q20):=by
    intro q18 q19 q20
    exact (((apc9 q18 q19 q20).symm).trans (((congrArg (fun t => t ◇ q20) (apc9 q18 q19 (q18 ◇ q19))).symm).trans (apc6 (q18 ◇ q19) q19 q20))).symm
  have apc12 : forall (q21 q22 q23 q24:G), (q22 ◇ q23) = (q21 ◇ q23):=by
    intro q21 q22 q23 q24
    exact ((apc10 q21 q22 q23).symm).trans ((((congrArg (fun t => t ◇ q23) ((h q21 q22 q24 ((q24 ◇ q21) ◇ q21)).symm)).symm).trans (apc9 q22 ((q24 ◇ q21) ◇ q21) q23)).trans ((congrArg (fun t => t ◇ q23) (apc10 q24 q21 q21)).trans (apc10 q21 q21 q23)))
  exact (apc12 (x ◇ y) x y (x ◇ y)).trans ((apc12 (x ◇ y) (y ◇ ((y ◇ y) ◇ y)) y (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49057_to_50704 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49057_to_50704
