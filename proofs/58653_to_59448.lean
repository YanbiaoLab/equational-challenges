-- Equation58653 → Equation59448
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ y = z ◇ (y ◇ (w ◇ u))
-- Conclusion: (x ◇ y) ◇ y = x ◇ ((z ◇ y) ◇ y)
-- Original submission SHA-256: c30b2a61ddaf831c160e0e7da5ae799a69628b666d75de3f74bdd99b456c50d5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ y = z ◇ (y ◇ (w ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = x ◇ ((z ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), ((y ◇ y) ◇ y) = ((x ◇ y) ◇ y):=by
    intro x y z w u
    exact ((h x y x x x).trans ((h y y x x x).symm)).symm
  have apc2 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((q0 ◇ q1) ◇ q1)) = ((q2 ◇ q3) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) ((h q0 q1 q3 q0 q0).symm)).symm).trans ((h q2 q3 q4 q1 (q0 ◇ q0)).symm)
  have apc3 : forall (q0 q1 q2 q3 q4:G), ((q2 ◇ q3) ◇ q3) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((apc2 q0 q0 q2 q3 q0).symm).trans (apc2 q0 q0 q0 q0 q0)
  have apc9 : forall (q5 q6 q7 q8:G), (q8 ◇ (q7 ◇ (q6 ◇ q5))) = ((q7 ◇ q7) ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc0 q5 q7 q5 q5 q5).trans (h q5 q7 q8 q6 q5)).symm
  have apc10 : forall (q9 q10 q11 q12:G), (q11 ◇ ((q9 ◇ q10) ◇ q10)) = ((q12 ◇ q12) ◇ q12):=by
    intro q9 q10 q11 q12
    exact (apc2 q9 q10 q9 q12 q11).trans ((apc0 q9 q12 q9 q9 q9).symm)
  have apc26 : forall (q13 q14 q0 q15 q16 q1 q4:G), (q4 ◇ ((q15 ◇ (q14 ◇ q13)) ◇ (q1 ◇ q16))) = ((q0 ◇ q15) ◇ q15):=by
    intro q13 q14 q0 q15 q16 q1 q4
    exact ((h q0 q15 (q13 ◇ (q15 ◇ (q14 ◇ q13))) q14 q13).trans (h q13 (q15 ◇ (q14 ◇ q13)) q4 q1 q16)).symm
  have apc31 : forall (q17 q18 q19 q20:G), ((q18 ◇ (q20 ◇ q19)) ◇ (q20 ◇ q19)) = ((q17 ◇ q17) ◇ q17):=by
    intro q17 q18 q19 q20
    exact (((apc9 q17 (q17 ◇ q17) q17 q17).symm).trans (((congrArg (fun t => q17 ◇ t) ((apc10 q17 q17 q17 (q20 ◇ q19)).symm)).symm).trans (apc26 q19 q20 q18 (q20 ◇ q19) q19 q20 q17))).symm
  have apc44 : forall (q13 q14 q15 q16 q1 q4:G), (q4 ◇ ((q15 ◇ (q14 ◇ q13)) ◇ (q1 ◇ q16))) = ((q15 ◇ q15) ◇ q15):=by
    intro q13 q14 q15 q16 q1 q4
    exact (((apc9 q13 q14 q15 ((q13 ◇ q15) ◇ q15)).symm).trans (((congrArg (fun t => t ◇ (q15 ◇ (q14 ◇ q13))) ((h q13 q15 q13 q14 q13).symm)).symm).trans (h q13 (q15 ◇ (q14 ◇ q13)) q4 q1 q16))).symm
  have apc61 : forall (q17 q18 q19 q20:G), ((q18 ◇ (q20 ◇ q19)) ◇ (q20 ◇ q19)) = ((q17 ◇ (q17 ◇ q17)) ◇ (q17 ◇ q17)):=by
    intro q17 q18 q19 q20
    exact (apc31 q17 q18 q19 q20).trans ((apc31 q17 q17 q17 q17).symm)
  have apc63 : forall (q21 q22 q23:G), ((q21 ◇ (q21 ◇ q21)) ◇ (q21 ◇ q21)) = ((q22 ◇ q23) ◇ q23):=by
    intro q21 q22 q23
    exact ((apc61 q21 (q21 ◇ q21) q21 q21).symm).trans ((apc3 (q21 ◇ q21) q21 q22 q23 q21).symm)
  have apc65 : forall (q24 q25 q26 q27 q28 q29:G), (q29 ◇ ((q26 ◇ q25) ◇ (q28 ◇ q27))) = (((q24 ◇ q24) ◇ q24) ◇ (q26 ◇ q25)):=by
    intro q24 q25 q26 q27 q28 q29
    exact (((congrArg (fun t => t ◇ (q26 ◇ q25)) (apc31 q24 q24 q25 q26)).symm).trans (h (q24 ◇ (q26 ◇ q25)) (q26 ◇ q25) q29 q28 q27)).symm
  have apc150 : forall (q24 q25 q26 q27 q28 q29:G), (q29 ◇ ((q26 ◇ q25) ◇ (q28 ◇ q27))) = (q24 ◇ ((q26 ◇ q25) ◇ (q24 ◇ q24))):=by
    intro q24 q25 q26 q27 q28 q29
    exact (apc65 q24 q25 q26 q27 q28 q29).trans ((apc65 q24 q25 q26 q24 q24 q24).symm)
  have apc152 : forall (q30 q31 q32:G), (q32 ◇ ((q30 ◇ q31) ◇ q31)) = ((q32 ◇ q32) ◇ q32):=by
    intro q30 q31 q32
    exact (((congrArg (fun t => q32 ◇ t) (apc63 q32 q30 q31)).symm).trans ((apc150 q32 (q32 ◇ q32) q32 q30 q30 q30).symm)).trans (apc44 q32 q32 q32 q30 q30 q30)
  exact (calc
    ((x ◇ y) ◇ y) = ((x ◇ x) ◇ x):=apc3 x x x y x
    _ = (x ◇ ((z ◇ y) ◇ y)):=(apc152 z y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58653_to_59448 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58653_to_59448
