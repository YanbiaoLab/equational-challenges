-- Equation45030 → Equation47484
-- Recorded verdict: true
-- Premise: x * y = z * ((w * (u * v)) * x)
-- Conclusion: x * y = (z * z) * ((z * x) * x)
-- Original submission SHA-256: eb13b4801bc9575ff60117dfebfc312a9f71b79b37c54d7cf375fe6c5c50f792
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = z ◇ ((w ◇ (u ◇ v)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ z) ◇ ((z ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (x y z w u v:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u v
    exact (h x y z w u v).trans ((h x x z w u v).symm)
  have apc3 : forall (q0 q1 q2 q3 q4 q5 q6:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact (((apc2 q0 q2 (q0 ◇ q2) (q0 ◇ q2) (q0 ◇ q2) (q0 ◇ q2)).symm).trans (((h q0 q2 q3 q0 q0 q0).trans (h q3 ((q0 ◇ (q0 ◇ q0)) ◇ q0) q1 q4 q5 q6)).trans (((congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q3) (congrArg (fun t => q4 ◇ t) (apc2 q5 q6 (q5 ◇ q6) (q5 ◇ q6) (q5 ◇ q6) (q5 ◇ q6))))).trans (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q3) (apc2 q4 (q5 ◇ q5) (q4 ◇ (q5 ◇ q5)) (q4 ◇ (q5 ◇ q5)) (q4 ◇ (q5 ◇ q5)) (q4 ◇ (q5 ◇ q5)))))).trans (apc2 q1 ((q4 ◇ q4) ◇ q3) (q1 ◇ ((q4 ◇ q4) ◇ q3)) (q1 ◇ ((q4 ◇ q4) ◇ q3)) (q1 ◇ ((q4 ◇ q4) ◇ q3)) (q1 ◇ ((q4 ◇ q4) ◇ q3)))))).symm
  have apc4 : forall (q7 q8 q9 q10 q11 q12:G), ((q7 ◇ q7) ◇ q8) = (q9 ◇ q9):=by
    intro q7 q8 q9 q10 q11 q12
    exact (((apc2 q9 (q10 ◇ q10) (q9 ◇ (q10 ◇ q10)) (q9 ◇ (q10 ◇ q10)) (q9 ◇ (q10 ◇ q10)) (q9 ◇ (q10 ◇ q10))).symm).trans ((((congrArg (fun t => q9 ◇ t) (apc3 q10 (q7 ◇ (q11 ◇ q12)) q10 q10 q10 q10 q10)).symm).trans ((h (q7 ◇ (q11 ◇ q12)) q8 q9 q7 q11 q12).symm)).trans ((congrArg (fun t => t ◇ q8) (congrArg (fun t => q7 ◇ t) (apc2 q11 q12 (q11 ◇ q12) (q11 ◇ q12) (q11 ◇ q12) (q11 ◇ q12)))).trans (congrArg (fun t => t ◇ q8) (apc2 q7 (q11 ◇ q11) (q7 ◇ (q11 ◇ q11)) (q7 ◇ (q11 ◇ q11)) (q7 ◇ (q11 ◇ q11)) (q7 ◇ (q11 ◇ q11))))))).symm
  have apc5 : forall (q13 q14:G), ((q13 ◇ q13) ◇ (q13 ◇ q13)) = (q14 ◇ q14):=by
    intro q13 q14
    exact (((apc4 q13 q13 q14 q13 q13 q13).symm).trans (apc2 (q13 ◇ q13) q13 q13 q13 q13 q13)).symm
  have apc12 : forall (q15 q16 q17 q18:G), (((q15 ◇ q15) ◇ q16) ◇ (q17 ◇ q17)) = (q18 ◇ q18):=by
    intro q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ (q17 ◇ q17)) ((apc4 q15 q16 q17 q15 q15 q15).symm)).symm).trans (apc5 q17 q18)
  have apc13 : forall (q19 q20 q21 q22 q23:G), (((q21 ◇ q21) ◇ q22) ◇ ((q19 ◇ q19) ◇ q20)) = (q23 ◇ q23):=by
    intro q19 q20 q21 q22 q23
    exact ((congrArg (fun t => ((q21 ◇ q21) ◇ q22) ◇ t) ((apc4 q19 q20 q19 q19 q19 q19).symm)).symm).trans (apc12 q21 q22 q19 q23)
  have apc14 : forall (q24 q25 q26:G), (q26 ◇ q26) = (q25 ◇ q24):=by
    intro q24 q25 q26
    exact ((h q25 q24 ((q24 ◇ q24) ◇ q24) (q24 ◇ q24) q24 q24).trans (apc13 (q24 ◇ q24) q25 q24 q24 q26)).symm
  exact ((apc14 y x (x ◇ y)).symm).trans (apc14 ((z ◇ x) ◇ x) (z ◇ z) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45030_to_47484 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45030_to_47484
