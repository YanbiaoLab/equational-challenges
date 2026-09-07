-- Equation46444 → Equation62480
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (y * (z * x))
-- Conclusion: (x * y) * z = ((w * y) * w) * w
-- Original submission SHA-256: fca01fa7b592667fd06cfd002e54f001f528ec58651c4929cf4cc79ed86adcfd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ x) ◇ (y ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((w ◇ y) ◇ w) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc4 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ (q2 ◇ q0))))) = ((q1 ◇ (q2 ◇ q0)) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ (q2 ◇ q0))))) ((h q0 q1 q2).symm)).symm).trans ((h (q1 ◇ (q2 ◇ q0)) q3 (q2 ◇ q0)).symm)
  have apc5 : forall (q4 q5 q6 q7:G), ((q4 ◇ q5) ◇ (q7 ◇ (q4 ◇ q5))) = ((q5 ◇ (q6 ◇ q4)) ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => (q4 ◇ q5) ◇ t) (congrArg (fun t => q7 ◇ t) ((h q4 q5 q6).symm))).symm).trans (apc4 q4 q5 q6 q7)
  have apc6 : forall (q8 q9 q10 q11:G), ((q9 ◇ (q8 ◇ q11)) ◇ q10) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((apc5 q11 q9 q8 q10).symm).trans ((h q9 q10 q11).symm)
  have apc7 : forall (q12 q13 q14 q15:G), ((q13 ◇ q12) ◇ q15) = ((q12 ◇ q14) ◇ q15):=by
    intro q12 q13 q14 q15
    exact (((congrArg (fun t => t ◇ q15) ((h q12 q14 q13).symm)).symm).trans (apc6 q14 (q13 ◇ q12) q15 (q13 ◇ q12))).symm
  have apc8 : forall (q16 q17 q18:G), ((q16 ◇ q17) ◇ q18) = (q17 ◇ q18):=by
    intro q16 q17 q18
    exact (apc7 q17 q16 (q16 ◇ q16) q18).trans (apc6 q16 q17 q18 q16)
  have apc9 : forall (q9 q10 q11 q8:G), (q11 ◇ q10) = (q9 ◇ q10):=by
    intro q9 q10 q11 q8
    exact (((apc8 q9 (q8 ◇ q11) q10).trans (apc8 q8 q11 q10)).symm).trans (apc6 q8 q9 q10 q11)
  have apc10 : forall (q0 q2 q19:G), (q0 ◇ (q2 ◇ q0)) = (q0 ◇ (q0 ◇ q19)):=by
    intro q0 q2 q19
    exact ((((apc8 q19 (q2 ◇ q0) (q0 ◇ q19)).trans (apc8 q2 q0 (q0 ◇ q19))).symm).trans ((((congrArg (fun t => (q19 ◇ (q2 ◇ q0)) ◇ t) ((h q0 q19 q2).symm)).symm).trans ((h (q2 ◇ q0) (q2 ◇ q0) q19).symm)).trans (apc8 q2 q0 (q2 ◇ q0)))).symm
  have apc12 : forall (q20 q21 q22 q23:G), (q21 ◇ (q21 ◇ q20)) = (q21 ◇ q22):=by
    intro q20 q21 q22 q23
    exact (((congrArg (fun t => (q23 ◇ q21) ◇ t) (apc8 q23 q21 q20)).trans (apc8 q23 q21 (q21 ◇ q20))).symm).trans (((apc10 (q23 ◇ q21) q22 q20).symm).trans ((h q21 q22 q23).symm))
  have apc13 : forall (q20 q21 q22 q23:G), (q21 ◇ q22) = (q21 ◇ q20):=by
    intro q20 q21 q22 q23
    exact ((apc12 q20 q21 q22 q23).symm).trans (apc12 q20 q21 q20 q23)
  have apc15 : forall (q24 q25 q26 q27:G), (q27 ◇ q24) = (q25 ◇ q26):=by
    intro q24 q25 q26 q27
    exact ((apc13 q24 q27 q26 q24).symm).trans (apc9 q25 q26 q27 q24)
  exact (apc15 z ((x ◇ y) ◇ z) (((w ◇ y) ◇ w) ◇ w) (x ◇ y)).trans ((apc15 w ((x ◇ y) ◇ z) (((w ◇ y) ◇ w) ◇ w) ((w ◇ y) ◇ w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46444_to_62480 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46444_to_62480
