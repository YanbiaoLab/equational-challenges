-- Equation43714 → Equation3737
-- Recorded verdict: true
-- Premise: x * y = y * ((z * x) * (x * w))
-- Conclusion: x * y = (x * z) * (y * z)
-- Original submission SHA-256: 4faf950571d95352adbfe43a9472456fb9edebe9708393c7ca10555372b40615
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ x) ◇ (x ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ z) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q3 ◇ q1) ◇ (q0 ◇ q1))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => (q3 ◇ q1) ◇ t) ((h q0 q1 q0 q0).symm))).symm).trans ((h q1 q2 q3 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q0 q4 q2 q3:G), (q2 ◇ (q0 ◇ (q3 ◇ (q4 ◇ q0)))) = ((q4 ◇ q0) ◇ q2):=by
    intro q0 q4 q2 q3
    exact ((cg (fun t => q2 ◇ t) ((h q0 (q3 ◇ (q4 ◇ q0)) q4 q0).symm)).symm).trans ((h (q4 ◇ q0) q2 q3 (q0 ◇ q0)).symm)
  have apc2 : forall (q5 q6 q7:G), (q7 ◇ (q6 ◇ q5)) = ((q6 ◇ q5) ◇ q7):=by
    intro q5 q6 q7
    exact ((cg (fun t => q7 ◇ t) ((h q6 q5 q5 q5).symm)).symm).trans (apc1 q5 q6 q7 (q5 ◇ q6))
  have apc3 : forall (q8 q9 q10:G), ((q9 ◇ q8) ◇ q10) = ((q8 ◇ q8) ◇ q10):=by
    intro q8 q9 q10
    exact (((apc2 q8 q8 q10).symm).trans (((cg (fun t => q10 ◇ t) (apc0 q9 q8 q8 q8)).symm).trans (apc1 q8 q9 q10 (q8 ◇ q8)))).symm
  have apc4 : forall (q11 q12 q13 q14:G), ((q11 ◇ (q14 ◇ q12)) ◇ q13) = (q12 ◇ q13):=by
    intro q11 q12 q13 q14
    exact ((apc1 (q14 ◇ q12) q11 q13 q12).symm).trans ((h q12 q13 q14 (q11 ◇ (q14 ◇ q12))).symm)
  have apc6 : forall (q15 q16 q17 q18 q19 q20:G), (q17 ◇ q16) = (q15 ◇ q16):=by
    intro q15 q16 q17 q18 q19 q20
    exact ((apc4 q18 q17 q16 q19).symm).trans ((((cg (fun t => t ◇ q16) (cg (fun t => q18 ◇ t) ((h q19 q17 q20 q15).symm))).symm).trans (apc4 q18 ((q20 ◇ q19) ◇ (q19 ◇ q15)) q16 q17)).trans ((((cg (fun t => t ◇ q16) (apc3 q19 q20 (q19 ◇ q15))).trans (apc3 (q19 ◇ q15) (q19 ◇ q19) q16)).trans (cg (fun t => t ◇ q16) (apc3 q15 q19 (q19 ◇ q15)))).trans (apc4 (q15 ◇ q15) q15 q16 q19)))
  have apc7 : forall (q21 q22 q23:G), ((q22 ◇ q22) ◇ q23) = (q21 ◇ q23):=by
    intro q21 q22 q23
    exact (((apc6 q21 q23 (q21 ◇ q22) q21 q21 q21).symm).trans (apc3 q22 q21 q23)).symm
  have apc8 : forall (q24 q25 q26 q27:G), ((q24 ◇ q26) ◇ q27) = (q25 ◇ q27):=by
    intro q24 q25 q26 q27
    exact ((cg (fun t => t ◇ q27) (apc6 q24 q26 q26 q24 q24 q24)).symm).trans (apc7 q25 q26 q27)
  have apc9 : forall (q15 q19 q20 q18 q16 q17:G), (q16 ◇ q16) = (q15 ◇ q16):=by
    intro q15 q19 q20 q18 q16 q17
    exact (((apc6 q15 q16 q17 q18 q19 q20).symm).trans (apc6 q16 q16 q17 q18 q19 q20)).symm
  have apc10 : forall (q28 q29 q30:G), ((q28 ◇ q29) ◇ q30) = (q30 ◇ q30):=by
    intro q28 q29 q30
    exact ((apc9 q28 q28 q28 q28 q30 q28).trans ((apc8 q28 q28 q29 q30).symm)).symm
  have apc11 : forall (q0 q31 q2 q3 q4 q32:G), (q2 ◇ ((q0 ◇ q3) ◇ (q31 ◇ q31))) = (q2 ◇ q2):=by
    intro q0 q31 q2 q3 q4 q32
    exact (((cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q3) ◇ t) (cg (fun t => t ◇ q31) (apc10 q4 q0 (q0 ◇ q32))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q3) ◇ t) (apc10 (q0 ◇ q32) (q0 ◇ q32) q31)))).symm).trans ((((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (((q4 ◇ q0) ◇ (q0 ◇ q32)) ◇ q31)) ((h q0 q3 q4 q32).symm))).symm).trans ((h ((q4 ◇ q0) ◇ (q0 ◇ q32)) q2 q3 q31).symm)).trans ((cg (fun t => t ◇ q2) (apc10 q4 q0 (q0 ◇ q32))).trans (apc10 (q0 ◇ q32) (q0 ◇ q32) q2)))
  have apc12 : forall (q33 q34 q35:G), ((q33 ◇ q34) ◇ (q33 ◇ q34)) = (q35 ◇ (q33 ◇ q34)):=by
    intro q33 q34 q35
    exact ((apc10 q33 q34 (q33 ◇ q34)).symm).trans (apc9 q35 q33 q33 q33 (q33 ◇ q34) q33)
  have apc13 : forall (q36 q37 q38 q39:G), ((q36 ◇ q38) ◇ (q37 ◇ q38)) = (q39 ◇ (q37 ◇ q38)):=by
    intro q36 q37 q38 q39
    exact ((cg (fun t => t ◇ (q37 ◇ q38)) (apc6 q36 q38 q37 q36 q36 q36)).symm).trans (apc12 q37 q38 q39)
  have apc15 : forall (q40 q41 q42 q43:G), ((q40 ◇ q42) ◇ (q41 ◇ q42)) = (q43 ◇ (q42 ◇ q42)):=by
    intro q40 q41 q42 q43
    exact (((cg (fun t => q43 ◇ t) ((apc9 q41 q40 q40 q40 q42 q40).symm)).symm).trans ((apc13 q40 q41 q42 q43).symm)).symm
  have apc16 : forall (q44 q45 q46 q47 q48 q49:G), ((q44 ◇ q45) ◇ (q44 ◇ q45)) = (q46 ◇ q46):=by
    intro q44 q45 q46 q47 q48 q49
    exact (((cg (fun t => t ◇ (q44 ◇ q45)) (cg (fun t => q47 ◇ t) (apc10 q48 q44 (q44 ◇ q49)))).trans (apc10 q47 ((q44 ◇ q49) ◇ (q44 ◇ q49)) (q44 ◇ q45))).symm).trans ((((cg (fun t => (q47 ◇ ((q48 ◇ q44) ◇ (q44 ◇ q49))) ◇ t) ((h q44 q45 q48 q49).symm)).symm).trans (apc15 q47 q45 ((q48 ◇ q44) ◇ (q44 ◇ q49)) q46)).trans (((cg (fun t => q46 ◇ t) (cg (fun t => t ◇ ((q48 ◇ q44) ◇ (q44 ◇ q49))) (apc10 q48 q44 (q44 ◇ q49)))).trans (cg (fun t => q46 ◇ t) (cg (fun t => ((q44 ◇ q49) ◇ (q44 ◇ q49)) ◇ t) (apc10 q48 q44 (q44 ◇ q49))))).trans (apc11 (q44 ◇ q49) (q44 ◇ q49) q46 (q44 ◇ q49) (q46 ◇ (((q44 ◇ q49) ◇ (q44 ◇ q49)) ◇ ((q44 ◇ q49) ◇ (q44 ◇ q49)))) (q46 ◇ (((q44 ◇ q49) ◇ (q44 ◇ q49)) ◇ ((q44 ◇ q49) ◇ (q44 ◇ q49)))))))
  have apc20 : forall (q50 q51 q52 q53:G), ((q50 ◇ q51) ◇ (q50 ◇ q51)) = (q52 ◇ q53):=by
    intro q50 q51 q52 q53
    exact (apc16 q50 q51 q53 q50 q50 q50).trans (apc6 q52 q53 q53 q50 q50 q50)
  exact ((apc20 (x ◇ y) ((x ◇ z) ◇ (y ◇ z)) x y).symm).trans (apc20 (x ◇ y) ((x ◇ z) ◇ (y ◇ z)) (x ◇ z) (y ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43714_to_3737 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43714_to_3737
