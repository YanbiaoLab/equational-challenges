-- Equation46525 → Equation53873
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (y * (w * x))
-- Conclusion: x * (x * y) = x * (y * (y * y))
-- Original submission SHA-256: 15038a4d9c5baf69361103c7f8adeb8f0be99b5eec9eefaeb7c6980e54c1746a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ (y ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = x ◇ (y ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), ((z ◇ y) ◇ (y ◇ (w ◇ x))) = ((x ◇ y) ◇ (y ◇ (x ◇ x))):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0 q0).symm).trans ((h q0 q1 q0 q0).symm)
  have apc2 : forall (q2 q3 q4:G), ((q4 ◇ (q2 ◇ q3)) ◇ (q2 ◇ q3)) = ((q2 ◇ q2) ◇ (q2 ◇ q3)):=by
    intro q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ (q2 ◇ q3)) ◇ t) (apc1 q2 q3)).symm).trans ((h (q2 ◇ q2) (q2 ◇ q3) q4 q3).symm)
  have apc4 : forall (q5 q6 q7:G), ((q7 ◇ q7) ◇ (q7 ◇ (q5 ◇ q6))) = ((q6 ◇ q7) ◇ (q7 ◇ (q5 ◇ q6))):=by
    intro q5 q6 q7
    exact (((congrArg (fun t => t ◇ (q7 ◇ (q5 ◇ q6))) ((h q6 q7 q5 q5).symm)).symm).trans (apc2 q7 (q5 ◇ q6) (q5 ◇ q7))).symm
  have apc5 : forall (q8 q9 q10 q11 q12:G), ((q9 ◇ q10) ◇ ((q10 ◇ (q8 ◇ q9)) ◇ (q11 ◇ q12))) = (q12 ◇ (q10 ◇ (q8 ◇ q9))):=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ ((q10 ◇ (q8 ◇ q9)) ◇ (q11 ◇ q12))) ((h q9 q10 q8 q8).symm)).symm).trans ((h q12 (q10 ◇ (q8 ◇ q9)) (q8 ◇ q10) q11).symm)
  have apc6 : forall (q13 q14 q15:G), ((q14 ◇ q15) ◇ (q15 ◇ (q13 ◇ q14))) = (q14 ◇ q15):=by
    intro q13 q14 q15
    exact ((apc4 q13 q14 q15).symm).trans ((h q14 q15 q15 q13).symm)
  have apc7 : forall (q5 q6 q7 q13 q14 q15:G), ((q7 ◇ q7) ◇ (q7 ◇ (q5 ◇ q6))) = (q6 ◇ q7):=by
    intro q5 q6 q7 q13 q14 q15
    exact (apc4 q5 q6 q7).trans (apc6 q5 q6 q7)
  have apc8 : forall (q16 q17 q18 q19 q20 q21:G), ((q18 ◇ (q16 ◇ q17)) ◇ (q21 ◇ (q19 ◇ q20))) = (q18 ◇ (q21 ◇ (q19 ◇ q20))):=by
    intro q16 q17 q18 q19 q20 q21
    exact (((apc5 q19 q20 q21 q17 q18).symm).trans (((congrArg (fun t => (q20 ◇ q21) ◇ t) (congrArg (fun t => (q21 ◇ (q19 ◇ q20)) ◇ t) ((h q17 q18 q16 q16).symm))).symm).trans (apc5 q19 q20 q21 (q16 ◇ q18) (q18 ◇ (q16 ◇ q17))))).symm
  have apc9 : forall (q22 q23 q24 q25:G), (q25 ◇ (q24 ◇ (q22 ◇ q23))) = (q23 ◇ q24):=by
    intro q22 q23 q24 q25
    exact (((apc8 q24 (q22 ◇ q23) q25 q22 q23 q24).symm).trans (apc2 q24 (q22 ◇ q23) q25)).trans (apc7 q22 q23 q24 ((q24 ◇ q24) ◇ (q24 ◇ (q22 ◇ q23))) ((q24 ◇ q24) ◇ (q24 ◇ (q22 ◇ q23))) ((q24 ◇ q24) ◇ (q24 ◇ (q22 ◇ q23))))
  have apc10 : forall (q26 q27 q28 q29:G), (q28 ◇ (q27 ◇ q27)) = (q28 ◇ q26):=by
    intro q26 q27 q28 q29
    exact ((apc9 q27 q28 (q27 ◇ q27) q29).symm).trans ((((congrArg (fun t => q29 ◇ t) (apc2 q27 q28 q26)).symm).trans (apc9 q27 q28 (q26 ◇ (q27 ◇ q28)) q29)).trans (apc9 q27 q28 q26 q28))
  exact ((apc10 (x ◇ y) (x ◇ (x ◇ y)) x (x ◇ (x ◇ y))).symm).trans (apc10 (y ◇ (y ◇ y)) (x ◇ (x ◇ y)) x (x ◇ (x ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46525_to_53873 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46525_to_53873
