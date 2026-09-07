-- Equation48244 → Equation59777
-- Recorded verdict: true
-- Premise: x * y = (z * (x * w)) * (u * x)
-- Conclusion: (x * y) * z = z * ((z * w) * w)
-- Original submission SHA-256: 78448ae851711d47804aa7f219d341dda411e72e72e6384a05ad2b08cd312a9d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (x ◇ w)) ◇ (u ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = z ◇ ((z ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q2 ◇ q0) ◇ (q1 ◇ q1)) = (q3 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q2 ◇ q0) ◇ t) (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3) (q1 ◇ q3))).symm).trans ((((congrArg (fun t => t ◇ (q1 ◇ q3)) ((h q2 q0 q0 q0 q3).symm)).symm).trans ((h q3 q4 (q0 ◇ (q2 ◇ q0)) q2 q1).symm)).trans (apc0 q3 q4 (q3 ◇ q4) (q3 ◇ q4) (q3 ◇ q4)))
  have apc2 : forall (q5 q6 q7 q8 q9 q10:G), ((q9 ◇ q9) ◇ (q7 ◇ q7)) = ((q6 ◇ q5) ◇ q8):=by
    intro q5 q6 q7 q8 q9 q10
    exact (((congrArg (fun t => (q9 ◇ (q10 ◇ q10)) ◇ t) (apc0 q7 (q6 ◇ q5) (q7 ◇ (q6 ◇ q5)) (q7 ◇ (q6 ◇ q5)) (q7 ◇ (q6 ◇ q5)))).trans (congrArg (fun t => t ◇ (q7 ◇ q7)) (apc0 q9 (q10 ◇ q10) (q9 ◇ (q10 ◇ q10)) (q9 ◇ (q10 ◇ q10)) (q9 ◇ (q10 ◇ q10))))).symm).trans (((congrArg (fun t => t ◇ (q7 ◇ (q6 ◇ q5))) (congrArg (fun t => q9 ◇ t) (apc1 q5 q5 q6 q10 q5))).symm).trans ((h (q6 ◇ q5) q8 q9 (q5 ◇ q5) q7).symm))
  have apc3 : forall (q11 q12 q13 q14:G), ((q12 ◇ q11) ◇ q13) = (q14 ◇ q14):=by
    intro q11 q12 q13 q14
    exact ((apc2 q11 q12 q11 q13 q11 q11).symm).trans (apc1 q11 q11 q11 q14 q11)
  have apc5 : forall (q15 q16 q17 q18 q19:G), ((q17 ◇ q16) ◇ q19) = (q18 ◇ q15):=by
    intro q15 q16 q17 q18 q19
    exact ((h q18 q15 (q18 ◇ q15) q15 q18).trans (apc2 q16 q17 q18 q19 (q18 ◇ q15) q15)).symm
  have apc7 : forall (q20 q21 q22 q23:G), ((q20 ◇ q20) ◇ q23) = (q22 ◇ q21):=by
    intro q20 q21 q22 q23
    exact ((congrArg (fun t => t ◇ q23) (apc3 q20 q20 q20 q20)).symm).trans (apc5 q21 q20 (q20 ◇ q20) q22 q23)
  exact ((apc7 ((x ◇ y) ◇ z) z (x ◇ y) (z ◇ ((z ◇ w) ◇ w))).symm).trans (apc7 ((x ◇ y) ◇ z) ((z ◇ w) ◇ w) z (z ◇ ((z ◇ w) ◇ w)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48244_to_59777 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48244_to_59777
