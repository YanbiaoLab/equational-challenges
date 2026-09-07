-- Equation58088 → Equation56741
-- Recorded verdict: true
-- Premise: x * (y * z) = ((w * y) * z) * y
-- Conclusion: x * (y * x) = (z * (y * z)) * y
-- Original submission SHA-256: 02b62b5fd251d449ba0212cd79fe3056575693c3dc7d97a91cdabb2e4eb321b8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = ((w ◇ y) ◇ z) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = (z ◇ (y ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ (y ◇ z)) = (x ◇ (y ◇ z)):=by
    intro x y z w
    exact ((h x y z x).trans ((h y y z x).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q1 ◇ (q2 ◇ q3)) = (q0 ◇ (q2 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((h q0 q2 q3 q0).trans ((h q1 q2 q3 q0).symm)).symm
  have apc2 : forall (q0 q1 q2 q3:G), ((q0 ◇ (q3 ◇ q2)) ◇ q2) = (q1 ◇ (q2 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h q0 q3 q2 q0).symm)).symm).trans ((h q1 q2 q3 (q0 ◇ q3)).symm)
  have apc5 : forall (q4 q5 q6 q7:G), (q6 ◇ ((q4 ◇ q5) ◇ q7)) = (q4 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7
    exact ((apc0 ((q4 ◇ (q4 ◇ q5)) ◇ q7) q4 q5 q4).trans ((h q6 (q4 ◇ q5) q7 q4).symm)).symm
  have apc6 : forall (q8 q9 q10 q11:G), (q10 ◇ (q10 ◇ q11)) = (q8 ◇ (q8 ◇ q9)):=by
    intro q8 q9 q10 q11
    exact ((((apc5 (q8 ◇ q9) q8 q8 q9).trans (apc5 q8 q9 (q8 ◇ q9) q8)).symm).trans (((congrArg (fun t => q8 ◇ t) (h (q10 ◇ q11) q9 q8 q8)).symm).trans (apc5 q10 q11 q8 (q9 ◇ q8)))).symm
  have apc9 : forall (q12 q13 q14 q15 q16:G), (q14 ◇ (q15 ◇ q16)) = (q12 ◇ (q12 ◇ q13)):=by
    intro q12 q13 q14 q15 q16
    exact (((apc6 q12 q13 q15 q16).symm).trans (apc0 q14 q15 q16 q12)).symm
  have apc16 : forall (q17 q18 q7:G), (((q17 ◇ q18) ◇ q7) ◇ q18) = (q18 ◇ (q18 ◇ q7)):=by
    intro q17 q18 q7
    exact ((apc0 q17 q18 q7 q17).trans (h q17 q18 q7 q17)).symm
  have apc17 : forall (q19 q20 q21:G), ((q19 ◇ (q21 ◇ q20)) ◇ q20) = (q20 ◇ (q20 ◇ q21)):=by
    intro q19 q20 q21
    exact (apc2 q19 q19 q20 q21).trans ((apc0 q19 q20 q21 q19).symm)
  have apc21 : forall (q22 q23 q24 q25:G), (q24 ◇ (q25 ◇ (q23 ◇ q25))) = (q22 ◇ (q25 ◇ q23)):=by
    intro q22 q23 q24 q25
    exact (((apc2 (q22 ◇ q25) q22 q25 q23).symm).trans ((h q24 q25 (q23 ◇ q25) q22).symm)).symm
  have apc22 : forall (q22 q23 q24 q25:G), (q23 ◇ (q25 ◇ q23)) = (q22 ◇ (q25 ◇ q23)):=by
    intro q22 q23 q24 q25
    exact (((apc21 q22 q23 q22 q25).symm).trans (apc21 q23 q23 q22 q25)).symm
  have apc24 : forall (q26 q27:G), (q27 ◇ (q26 ◇ q27)) = (q26 ◇ (q26 ◇ q27)):=by
    intro q26 q27
    exact (apc22 q26 q27 q26 q26).trans ((apc0 q26 q26 q27 q26).symm)
  have apc50 : forall (q4 q5 q6 q18:G), (q6 ◇ (q18 ◇ (q4 ◇ q5))) = ((q4 ◇ (q4 ◇ q5)) ◇ q18):=by
    intro q4 q5 q6 q18
    exact (((congrArg (fun t => t ◇ q18) ((apc0 (q4 ◇ q18) q4 q5 q4).symm)).symm).trans ((h q6 q18 (q4 ◇ q5) q4).symm)).symm
  have apc56 : forall (q28 q29:G), ((q28 ◇ (q28 ◇ q29)) ◇ q28) = (q28 ◇ (q28 ◇ q29)):=by
    intro q28 q29
    exact (((congrArg (fun t => q28 ◇ t) (apc5 q28 q29 q28 q28)).trans (apc50 q28 q29 q28 q28)).symm).trans (((congrArg (fun t => q28 ◇ t) (apc0 q28 (q28 ◇ q29) q28 q28)).symm).trans (apc5 q28 q29 q28 ((q28 ◇ q29) ◇ q28)))
  have apc57 : forall (q30 q31:G), (q31 ◇ (q31 ◇ q30)) = (q30 ◇ (q30 ◇ q31)):=by
    intro q30 q31
    exact ((((congrArg (fun t => t ◇ q31) (apc50 q30 q31 q31 q30)).trans (congrArg (fun t => t ◇ q31) (apc56 q30 q31))).trans (apc17 q30 q31 q30)).symm).trans ((((congrArg (fun t => t ◇ q31) (congrArg (fun t => q31 ◇ t) (apc24 q30 q31))).symm).trans (apc56 q31 (q30 ◇ q31))).trans (((congrArg (fun t => q31 ◇ t) (apc24 q30 q31)).trans (apc50 q30 q31 q31 q30)).trans (apc56 q30 q31)))
  have apc67 : forall (q32 q33 q34 q35:G), (q35 ◇ (q32 ◇ (q34 ◇ q33))) = (q33 ◇ (q33 ◇ q34)):=by
    intro q32 q33 q34 q35
    exact (((congrArg (fun t => q35 ◇ t) (apc21 q32 q33 (q33 ◇ q34) q34)).symm).trans (apc21 q32 q34 q35 (q33 ◇ q34))).trans (apc5 q33 q34 q32 q34)
  have apc70 : forall (q36 q37 q38 q39:G), ((q36 ◇ (q37 ◇ q38)) ◇ q39) = (q37 ◇ (q37 ◇ q38)):=by
    intro q36 q37 q38 q39
    exact (((congrArg (fun t => t ◇ q39) (apc1 q36 (q36 ◇ q39) q37 q38)).symm).trans (apc16 q36 q39 (q37 ◇ q38))).trans ((apc67 q39 q38 q37 q39).trans (apc57 q37 q38))
  exact (calc
    (x ◇ (y ◇ x)) = (y ◇ (y ◇ z)):=apc9 y z x y x
    _ = ((z ◇ (y ◇ z)) ◇ y):=(apc70 z y z y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58088_to_56741 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58088_to_56741
