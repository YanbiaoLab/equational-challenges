-- Equation53668 → Equation44076
-- Recorded verdict: true
-- Premise: x * y = (((z * w) * x) * x) * z
-- Conclusion: x * y = z * ((w * z) * (y * x))
-- Original submission SHA-256: d6cfff42abab72021964e0a7101b9663f0fe9f8a31943c5a21be6d9ef13dd34b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ x) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ z) ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q2 ◇ q1) ◇ (q2 ◇ q0)) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ (q2 ◇ q0)) ((h q2 q1 q2 q0).symm)).symm).trans ((h q2 q3 (q2 ◇ q0) q2).symm)).trans (apc0 q2 q3 (q2 ◇ q3) (q2 ◇ q3))
  have apc2 : forall (q4 q5 q6 q7 q8:G), (q5 ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5 q6 q7 q8
    exact (((((congrArg (fun t => t ◇ ((((q5 ◇ q6) ◇ q4) ◇ q4) ◇ q7)) (apc0 q4 q8 (q4 ◇ q8) (q4 ◇ q8))).trans (apc0 (q4 ◇ q4) ((((q5 ◇ q6) ◇ q4) ◇ q4) ◇ q7) ((q4 ◇ q4) ◇ ((((q5 ◇ q6) ◇ q4) ◇ q4) ◇ q7)) ((q4 ◇ q4) ◇ ((((q5 ◇ q6) ◇ q4) ◇ q4) ◇ q7)))).trans (apc1 q4 q4 q4 ((q4 ◇ q4) ◇ (q4 ◇ q4)))).symm).trans ((((congrArg (fun t => t ◇ ((((q5 ◇ q6) ◇ q4) ◇ q4) ◇ q7)) ((h q4 q8 q5 q6).symm)).symm).trans (apc1 q7 q5 (((q5 ◇ q6) ◇ q4) ◇ q4) q6)).trans (((apc1 q4 q4 ((q5 ◇ q6) ◇ q4) ((((q5 ◇ q6) ◇ q4) ◇ q4) ◇ (((q5 ◇ q6) ◇ q4) ◇ q4))).trans (apc1 q4 q4 (q5 ◇ q6) (((q5 ◇ q6) ◇ q4) ◇ ((q5 ◇ q6) ◇ q4)))).trans (apc1 q6 q6 q5 ((q5 ◇ q6) ◇ (q5 ◇ q6)))))).symm
  have apc4 : forall (x y z w:G), ((((z ◇ w) ◇ x) ◇ x) ◇ z) = ((((x ◇ x) ◇ x) ◇ x) ◇ x):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc6 : forall (q9 q10 q11:G), ((q9 ◇ q9) ◇ q10) = (q10 ◇ q10):=by
    intro q9 q10 q11
    exact (((congrArg (fun t => t ◇ q10) (apc0 (q9 ◇ q9) (q10 ◇ q11) ((q9 ◇ q9) ◇ (q10 ◇ q11)) ((q9 ◇ q9) ◇ (q10 ◇ q11)))).trans (congrArg (fun t => t ◇ q10) (apc1 q9 q9 q9 ((q9 ◇ q9) ◇ (q9 ◇ q9))))).symm).trans ((((congrArg (fun t => t ◇ q10) (congrArg (fun t => t ◇ (q10 ◇ q11)) (apc2 q9 (q10 ◇ q11) q9 q9 q9))).symm).trans (apc4 (q10 ◇ q11) q9 q10 q11)).trans ((((congrArg (fun t => t ◇ (q10 ◇ q11)) (congrArg (fun t => t ◇ (q10 ◇ q11)) (congrArg (fun t => t ◇ (q10 ◇ q11)) (apc1 q11 q11 q10 ((q10 ◇ q11) ◇ (q10 ◇ q11)))))).trans (congrArg (fun t => t ◇ (q10 ◇ q11)) (congrArg (fun t => t ◇ (q10 ◇ q11)) (apc1 q11 q10 q10 ((q10 ◇ q10) ◇ (q10 ◇ q11)))))).trans (congrArg (fun t => t ◇ (q10 ◇ q11)) (apc1 q11 q10 q10 ((q10 ◇ q10) ◇ (q10 ◇ q11))))).trans (apc1 q11 q10 q10 ((q10 ◇ q10) ◇ (q10 ◇ q11)))))
  have apc7 : forall (q12 q13 q14:G), ((q14 ◇ q12) ◇ q13) = (q14 ◇ q14):=by
    intro q12 q13 q14
    exact ((((congrArg (fun t => t ◇ q14) (apc1 q12 q12 q14 ((q14 ◇ q12) ◇ (q14 ◇ q12)))).trans (apc6 q14 q14 ((q14 ◇ q14) ◇ q14))).symm).trans (((congrArg (fun t => t ◇ q14) (apc6 (q14 ◇ q12) (q14 ◇ q12) q12)).symm).trans ((h (q14 ◇ q12) q13 q14 q12).symm))).symm
  have apc8 : forall (q15 q16 q17 q18:G), (q17 ◇ q17) = (q16 ◇ q15):=by
    intro q15 q16 q17 q18
    exact (((h q16 q15 q17 q18).trans (apc7 q16 q17 ((q17 ◇ q18) ◇ q16))).trans (((congrArg (fun t => t ◇ ((q17 ◇ q18) ◇ q16)) (apc7 q18 q16 q17)).trans (congrArg (fun t => (q17 ◇ q17) ◇ t) (apc7 q18 q16 q17))).trans (apc7 q17 (q17 ◇ q17) q17))).symm
  exact ((apc8 y x (x ◇ y) (x ◇ y)).symm).trans (apc8 ((w ◇ z) ◇ (y ◇ x)) z (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53668_to_44076 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53668_to_44076
