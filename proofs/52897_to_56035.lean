-- Equation52897 → Equation56035
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * u)) * x) * u
-- Conclusion: x * (y * y) = (z * z) * (w * x)
-- Original submission SHA-256: 0357a142e4e63043b83c0a441f3da72934ea4ce786b3ee7bb2d635f2d4a92070
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (w ◇ u)) ◇ x) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ z) ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), (((q0 ◇ q0) ◇ q2) ◇ q1) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) (apc1 q0 q3 (q0 ◇ q3) (q0 ◇ q3) (q0 ◇ q3)))).symm).trans ((((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) ((h q0 q3 q0 q0 (q0 ◇ q1)).symm))).symm).trans ((h q2 q4 ((q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ q0) q0 q1).symm)).trans (apc1 q2 q4 (q2 ◇ q4) (q2 ◇ q4) (q2 ◇ q4)))
  have apc3 : forall (q5 q6 q7 q8 q9:G), (q6 ◇ q6) = (q5 ◇ q5):=by
    intro q5 q6 q7 q8 q9
    exact (((((congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ q5) (congrArg (fun t => q8 ◇ t) (apc1 q9 q6 (q9 ◇ q6) (q9 ◇ q6) (q9 ◇ q6))))).trans (congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ q5) (apc1 q8 (q9 ◇ q9) (q8 ◇ (q9 ◇ q9)) (q8 ◇ (q9 ◇ q9)) (q8 ◇ (q9 ◇ q9)))))).trans (apc2 q8 q7 q5 (((q8 ◇ q8) ◇ q5) ◇ q7) (((q8 ◇ q8) ◇ q5) ◇ q7))).symm).trans (((congrArg (fun t => t ◇ q7) ((h (q8 ◇ (q9 ◇ q6)) q5 q8 q9 q6).symm)).symm).trans (apc2 (q8 ◇ (q9 ◇ q6)) q7 q6 q9 q9))).symm
  have apc5 : forall (q10 q11 q12 q13 q14:G), ((q13 ◇ q13) ◇ q12) = ((q10 ◇ q10) ◇ q11):=by
    intro q10 q11 q12 q13 q14
    exact ((((congrArg (fun t => t ◇ q11) (apc3 q10 (q13 ◇ (q14 ◇ q11)) q10 q10 q10)).symm).trans ((h (q13 ◇ (q14 ◇ q11)) q12 q13 q14 q11).symm)).trans (congrArg (fun t => t ◇ q12) (apc1 q13 (q14 ◇ q11) (q13 ◇ (q14 ◇ q11)) (q13 ◇ (q14 ◇ q11)) (q13 ◇ (q14 ◇ q11))))).symm
  have apc9 : forall (q10 q11 q12 q13 q14:G), ((q12 ◇ q12) ◇ q12) = ((q10 ◇ q10) ◇ q11):=by
    intro q10 q11 q12 q13 q14
    exact (((apc5 q10 q11 q12 q13 q14).symm).trans (apc5 q12 q12 q12 q13 q14)).symm
  have apc13 : forall (q15 q16 q17 q18 q19:G), ((q17 ◇ q16) ◇ q18) = (q15 ◇ q15):=by
    intro q15 q16 q17 q18 q19
    exact (((apc2 q19 q16 q15 (((q19 ◇ q19) ◇ q15) ◇ q16) (((q19 ◇ q19) ◇ q15) ◇ q16)).symm).trans (((congrArg (fun t => t ◇ q16) (apc9 q19 q15 (q17 ◇ q16) q19 q19)).symm).trans ((h (q17 ◇ q16) q18 (q17 ◇ q16) q17 q16).symm))).symm
  have apc14 : forall (q20 q21 q22:G), (q22 ◇ q20) = (q21 ◇ q21):=by
    intro q20 q21 q22
    exact (h q22 q20 q20 q20 q20).trans (apc13 q21 q22 (q20 ◇ (q20 ◇ q20)) q20 q20)
  exact (apc14 (y ◇ y) (x ◇ (y ◇ y)) x).trans ((apc14 (w ◇ x) (x ◇ (y ◇ y)) (z ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52897_to_56035 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52897_to_56035
