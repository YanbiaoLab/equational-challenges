-- Equation18493 → Equation41726
-- Recorded verdict: true
-- Premise: x = (y * z) * (y * ((w * z) * x))
-- Conclusion: x * x = y * (z * (w * (u * x)))
-- Original submission SHA-256: 535eb8356a8185ee1ef45b423c42b8b475d1c94473e63e20aef981e72fb6b358
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (y ◇ ((w ◇ z) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ (z ◇ (w ◇ (u ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q2 ◇ ((q0 ◇ q4) ◇ q1)) = ((q3 ◇ q4) ◇ (q3 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => (q3 ◇ q4) ◇ t) (congrArg (fun t => q3 ◇ t) ((h q1 q2 q4 q0).symm))).symm).trans ((h (q2 ◇ ((q0 ◇ q4) ◇ q1)) q3 q4 q2).symm)).symm
  have apc2 : forall (q0 q1 q2 q3 q4:G), (q2 ◇ ((q0 ◇ q4) ◇ q1)) = (q1 ◇ ((q1 ◇ q4) ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (apc0 q0 q1 q2 q0 q4).trans ((apc0 q1 q1 q1 q0 q4).symm)
  have apc3 : forall (q5 q6 q7 q8:G), (q7 ◇ ((q7 ◇ q8) ◇ q7)) = ((q5 ◇ q6) ◇ (q5 ◇ q7)):=by
    intro q5 q6 q7 q8
    exact ((((apc0 q5 q7 ((q5 ◇ q6) ◇ q8) q5 q6).symm).trans ((apc0 q5 q7 q5 (q5 ◇ q6) q8).symm)).trans (apc2 q5 q7 q5 (q5 ◇ ((q5 ◇ q8) ◇ q7)) q8)).symm
  have apc9 : forall (q9 q10 q11 q12 q13:G), (q12 ◇ ((q12 ◇ q13) ◇ q12)) = (q9 ◇ ((q10 ◇ q11) ◇ q12)):=by
    intro q9 q10 q11 q12 q13
    exact (((congrArg (fun t => t ◇ ((q10 ◇ q11) ◇ q12)) ((h q9 q10 q11 q9).symm)).symm).trans ((apc3 (q10 ◇ q11) (q10 ◇ ((q9 ◇ q11) ◇ q9)) q12 q13).symm)).symm
  have apc10 : forall (q14 q15 q16 q17:G), (q16 ◇ ((q16 ◇ q17) ◇ q16)) = (q15 ◇ (q14 ◇ q16)):=by
    intro q14 q15 q16 q17
    exact (((congrArg (fun t => q15 ◇ t) (congrArg (fun t => t ◇ q16) ((h q14 q14 q14 q14).symm))).symm).trans ((apc9 q15 (q14 ◇ q14) (q14 ◇ ((q14 ◇ q14) ◇ q14)) q16 q17).symm)).symm
  have apc11 : forall (q14 q15 q16 q17:G), (q16 ◇ (q16 ◇ q16)) = (q15 ◇ (q14 ◇ q16)):=by
    intro q14 q15 q16 q17
    exact (((apc10 q14 q15 q16 q14).symm).trans (apc10 q16 q16 q16 q14)).symm
  have apc12 : forall (q18 q19 q20 q21 q22:G), (q21 ◇ (q20 ◇ q22)) = (q19 ◇ (q18 ◇ q22)):=by
    intro q18 q19 q20 q21 q22
    exact (((apc10 q18 q19 q22 q18).symm).trans (apc10 q20 q21 q22 q18)).symm
  have apc13 : forall (q18 q19 q20 q21 q22:G), (q20 ◇ (q20 ◇ q22)) = (q19 ◇ (q18 ◇ q22)):=by
    intro q18 q19 q20 q21 q22
    exact (((apc12 q18 q19 q20 q18 q22).symm).trans (apc12 q20 q20 q20 q18 q22)).symm
  have apc16 : forall (q0 q1 q23 q2 q4:G), ((((q2 ◇ q4) ◇ q23) ◇ q4) ◇ q1) = ((q0 ◇ q23) ◇ q1):=by
    intro q0 q1 q23 q2 q4
    exact ((congrArg (fun t => (((q2 ◇ q4) ◇ q23) ◇ q4) ◇ t) ((h q1 (q2 ◇ q4) q23 q0).symm)).symm).trans ((h ((q0 ◇ q23) ◇ q1) ((q2 ◇ q4) ◇ q23) q4 q2).symm)
  have apc17 : forall (q0 q1 q23 q2 q4:G), ((q1 ◇ q23) ◇ q1) = ((q0 ◇ q23) ◇ q1):=by
    intro q0 q1 q23 q2 q4
    exact (((apc16 q0 q1 q23 q0 q0).symm).trans (apc16 q1 q1 q23 q0 q0)).symm
  have apc19 : forall (q24 q25 q26 q27:G), ((q25 ◇ q27) ◇ q25) = ((q24 ◇ q26) ◇ q25):=by
    intro q24 q25 q26 q27
    exact (apc17 ((q24 ◇ q27) ◇ q26) q25 q27 q24 q24).trans (apc16 q24 q25 q26 q24 q27)
  have apc21 : forall (q28 q29 q30:G), ((q29 ◇ q30) ◇ q29) = (q28 ◇ q29):=by
    intro q28 q29 q30
    exact (((congrArg (fun t => t ◇ q29) ((h q28 q28 q28 q28).symm)).symm).trans ((apc19 (q28 ◇ q28) q29 (q28 ◇ ((q28 ◇ q28) ◇ q28)) q30).symm)).symm
  have apc22 : forall (q28 q29 q30:G), (q29 ◇ q29) = (q28 ◇ q29):=by
    intro q28 q29 q30
    exact (((apc21 q28 q29 q28).symm).trans (apc21 q29 q29 q28)).symm
  have apc23 : forall (q31 q32 q33:G), (q32 ◇ q33) = (q31 ◇ q33):=by
    intro q31 q32 q33
    exact (((apc21 q31 q33 q31).symm).trans (apc21 q32 q33 q31)).symm
  have apc32 : forall (q34 q35 q36:G), ((q34 ◇ q36) ◇ q35) = (q35 ◇ q35):=by
    intro q34 q35 q36
    exact ((apc22 (q35 ◇ q36) q35 q34).trans (apc17 q34 q35 q36 q34 q34)).symm
  have apc40 : forall (x y z w:G), ((y ◇ z) ◇ (y ◇ (x ◇ x))) = ((x ◇ x) ◇ (x ◇ (x ◇ x))):=by
    intro x y z w
    exact ((congrArg (fun t => (y ◇ z) ◇ t) (congrArg (fun t => y ◇ t) (apc32 w x z))).symm).trans ((((h x y z w).symm).trans (h x x x x)).trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (apc32 x x x))))
  have apc41 : forall (q37:G), ((q37 ◇ q37) ◇ (q37 ◇ (q37 ◇ q37))) = q37:=by
    intro q37
    exact ((((congrArg (fun t => ((q37 ◇ q37) ◇ (q37 ◇ (q37 ◇ q37))) ◇ t) (congrArg (fun t => (q37 ◇ q37) ◇ t) (apc32 q37 q37 (q37 ◇ (q37 ◇ q37))))).trans (apc32 (q37 ◇ q37) ((q37 ◇ q37) ◇ (q37 ◇ q37)) (q37 ◇ (q37 ◇ q37)))).trans (apc40 q37 (q37 ◇ q37) (q37 ◇ q37) (((q37 ◇ q37) ◇ (q37 ◇ q37)) ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))))).symm).trans (((congrArg (fun t => t ◇ ((q37 ◇ q37) ◇ ((q37 ◇ (q37 ◇ (q37 ◇ q37))) ◇ q37))) (apc40 q37 q37 q37 q37)).symm).trans ((h q37 (q37 ◇ q37) (q37 ◇ (q37 ◇ q37)) q37).symm))
  have apc46 : forall (q38 q39:G), (q39 ◇ (q38 ◇ (q38 ◇ q38))) = q38:=by
    intro q38 q39
    exact (((apc41 q38).symm).trans (apc23 q39 (q38 ◇ q38) (q38 ◇ (q38 ◇ q38)))).symm
  have apc57 : forall (q40 q41 q42 q43:G), (q43 ◇ (q41 ◇ (q40 ◇ q42))) = q42:=by
    intro q40 q41 q42 q43
    exact ((congrArg (fun t => q43 ◇ t) (apc11 q40 q41 q42 q40)).symm).trans (apc46 q42 q43)
  exact (calc
    (x ◇ x) = (u ◇ x):=apc22 u x u
    _ = (u ◇ (u ◇ (w ◇ (u ◇ x)))):=(apc57 w u (u ◇ x) u).symm
    _ = (y ◇ (z ◇ (w ◇ (u ◇ x)))):=((apc13 z y u u (w ◇ (u ◇ x))).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18493_to_41726 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18493_to_41726
