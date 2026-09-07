-- Equation60390 → Equation60324
-- Recorded verdict: true
-- Premise: (x * y) * y = (z * x) * (w * u)
-- Conclusion: (x * y) * y = (x * z) * (y * x)
-- Original submission SHA-256: 15612a1dfa87320d92e19a761e6c0187a0daccabcfbe58be64fc508a3c3f34e3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ y = (z ◇ x) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (x ◇ z) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), ((x ◇ y) ◇ y) = ((x ◇ x) ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ (q1 ◇ q0)) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2 q3
    exact (((apc0 q2 q0 q0 q0 q0).symm).trans (h q2 q0 q3 q1 q0)).symm
  have apc3 : forall (q4 q5 q6 q7 q8 q9 q10:G), (((q5 ◇ q4) ◇ q7) ◇ q7) = ((q6 ◇ q6) ◇ q6):=by
    intro q4 q5 q6 q7 q8 q9 q10
    exact ((((congrArg (fun t => t ◇ (q8 ◇ q9)) (apc0 q6 q10 ((q6 ◇ q10) ◇ q10) ((q6 ◇ q10) ◇ q10) ((q6 ◇ q10) ◇ q10))).trans (apc1 q9 q8 q6 (q6 ◇ q6))).symm).trans (((congrArg (fun t => t ◇ (q8 ◇ q9)) ((h q6 q10 q4 q5 q4).symm)).symm).trans ((h (q5 ◇ q4) q7 (q4 ◇ q6) q8 q9).symm))).symm
  have apc6 : forall (q11 q12 q13 q14 q15 q16:G), (((q11 ◇ q11) ◇ q11) ◇ q13) = ((q12 ◇ q12) ◇ q12):=by
    intro q11 q12 q13 q14 q15 q16
    exact ((congrArg (fun t => t ◇ q13) (apc1 q14 q15 q11 q16)).symm).trans (((congrArg (fun t => t ◇ q13) (h q11 q13 q16 q15 q14)).symm).trans (apc3 q13 q11 q12 q13 q14 q14 q14))
  have apc7 : forall (q17 q18 q19:G), ((q19 ◇ q19) ◇ q19) = ((q18 ◇ q17) ◇ q17):=by
    intro q17 q18 q19
    exact ((h q18 q17 (q18 ◇ q18) q17 q17).trans (apc6 q18 q19 (q17 ◇ q17) q17 q17 q17)).symm
  have apc8 : forall (q20 q21 q22 q23:G), ((q23 ◇ q22) ◇ q22) = ((q21 ◇ q20) ◇ q20):=by
    intro q20 q21 q22 q23
    exact (((apc7 q20 q21 q20).symm).trans (apc7 q22 q23 q20)).symm
  exact (calc
    ((x ◇ y) ◇ y) = ((z ◇ x) ◇ x):=apc8 x z y x
    _ = ((x ◇ z) ◇ (y ◇ x)):=((h z x x y x).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60390_to_60324 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60390_to_60324
