-- Equation23378 → Equation23474
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ y) ◇ (z ◇ (y ◇ z))
-- Conclusion: x = ((y ◇ y) ◇ x) ◇ (x ◇ (z ◇ z))
-- Original submission SHA-256: 9a4ab6cea49bd0a1d8b89f23b2687be43d22750e551de7209276f2cf661bff20
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ (z ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ x) ◇ (x ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1))) ((h (q0 ◇ q0) q0 q0).symm)).symm).trans ((h q0 (q0 ◇ (q0 ◇ q0)) q1).symm)
  have apc3 : forall (q2 q3 q4:G), ((q2 ◇ (q2 ◇ q2)) ◇ (q4 ◇ ((q2 ◇ q2) ◇ q4))) = (q3 ◇ ((q2 ◇ (q2 ◇ q2)) ◇ q3)):=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ (q4 ◇ ((q2 ◇ q2) ◇ q4))) (cg (fun t => t ◇ (q2 ◇ q2)) (apc0 q2 q3))).symm).trans ((h (q3 ◇ ((q2 ◇ (q2 ◇ q2)) ◇ q3)) (q2 ◇ q2) q4).symm)
  have apc4 : forall (q2 q3 q4:G), (q3 ◇ ((q2 ◇ (q2 ◇ q2)) ◇ q3)) = (q2 ◇ ((q2 ◇ (q2 ◇ q2)) ◇ q2)):=by
    intro q2 q3 q4
    exact ((apc3 q2 q3 q2).symm).trans (apc3 q2 q2 q2)
  have apc5 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) = q0:=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (apc4 q0 q0 (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)))).symm).trans (apc0 q0 q0)
  have apc7 : forall (q5 q6 q7 q1:G), ((q5 ◇ ((q6 ◇ q5) ◇ q6)) ◇ (q1 ◇ (((q6 ◇ q5) ◇ q6) ◇ q1))) = (q7 ◇ (q6 ◇ q7)):=by
    intro q5 q6 q7 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (((q6 ◇ q5) ◇ q6) ◇ q1))) (cg (fun t => t ◇ ((q6 ◇ q5) ◇ q6)) ((h q5 q6 q7).symm))).symm).trans ((h (q7 ◇ (q6 ◇ q7)) ((q6 ◇ q5) ◇ q6) q1).symm)
  have apc8 : forall (q5 q6 q7 q1:G), (q7 ◇ (q6 ◇ q7)) = (q5 ◇ (q6 ◇ q5)):=by
    intro q5 q6 q7 q1
    exact ((apc7 q5 q6 q7 q5).symm).trans (apc7 q5 q6 q5 q5)
  have apc9 : forall (q5 q6 q7 q1:G), (q6 ◇ (q6 ◇ q6)) = (q5 ◇ (q6 ◇ q5)):=by
    intro q5 q6 q7 q1
    exact (((apc8 q5 q6 q5 q5).symm).trans (apc8 q6 q6 q5 q5)).symm
  have apc10 : forall (q8 q9 q10 q11:G), ((q9 ◇ q11) ◇ (q8 ◇ (q9 ◇ q8))) = (q10 ◇ (q11 ◇ q10)):=by
    intro q8 q9 q10 q11
    exact ((cg (fun t => (q9 ◇ q11) ◇ t) (apc8 q8 q9 q11 q8)).symm).trans (apc8 q10 q11 (q9 ◇ q11) q8)
  have apc11 : forall (q12 q13 q14 q15:G), (q15 ◇ (((q13 ◇ q12) ◇ q13) ◇ q15)) = ((q14 ◇ (q13 ◇ q14)) ◇ q12):=by
    intro q12 q13 q14 q15
    exact (((cg (fun t => (q14 ◇ (q13 ◇ q14)) ◇ t) ((h q12 q13 q14).symm)).symm).trans (apc8 q15 ((q13 ◇ q12) ◇ q13) (q14 ◇ (q13 ◇ q14)) q12)).symm
  have apc12 : forall (q12 q13 q14 q15:G), ((q14 ◇ (q13 ◇ q14)) ◇ q12) = ((q12 ◇ (q13 ◇ q12)) ◇ q12):=by
    intro q12 q13 q14 q15
    exact ((apc11 q12 q13 q14 q12).symm).trans (apc11 q12 q13 q12 q12)
  have apc23 : forall (q16 q17 q18:G), (q18 ◇ (((q17 ◇ q16) ◇ q17) ◇ q18)) = ((q16 ◇ (q17 ◇ q16)) ◇ q16):=by
    intro q16 q17 q18
    exact (((apc12 q16 q17 q17 ((q17 ◇ (q17 ◇ q17)) ◇ q16)).symm).trans (((cg (fun t => t ◇ q16) ((apc9 q16 q17 q16 q16).symm)).symm).trans ((apc11 q16 q17 q16 q18).symm))).symm
  have apc25 : forall (q19 q20 q21:G), (q21 ◇ ((q19 ◇ (q20 ◇ q19)) ◇ q21)) = (q20 ◇ ((q20 ◇ (q20 ◇ q20)) ◇ q20)):=by
    intro q19 q20 q21
    exact ((cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q21) (apc8 q19 q20 q20 q19))).symm).trans (apc4 q20 q21 q19)
  have apc35 : forall (q22 q23 q24 q25 q26:G), ((q22 ◇ (q23 ◇ q22)) ◇ (q24 ◇ (q25 ◇ q24))) = (q26 ◇ ((q23 ◇ q25) ◇ q26)):=by
    intro q22 q23 q24 q25 q26
    exact ((cg (fun t => (q22 ◇ (q23 ◇ q22)) ◇ t) (apc10 q22 q23 q24 q25)).symm).trans (apc8 q26 (q23 ◇ q25) (q22 ◇ (q23 ◇ q22)) q22)
  have apc36 : forall (q22 q23 q24 q25 q26:G), (q26 ◇ ((q23 ◇ q25) ◇ q26)) = (q22 ◇ ((q23 ◇ q25) ◇ q22)):=by
    intro q22 q23 q24 q25 q26
    exact ((apc35 q22 q23 q22 q25 q26).symm).trans (apc35 q22 q23 q22 q25 q22)
  have apc37 : forall (q22 q23 q24 q25 q26:G), (q23 ◇ ((q23 ◇ q25) ◇ q23)) = (q22 ◇ ((q23 ◇ q25) ◇ q22)):=by
    intro q22 q23 q24 q25 q26
    exact (((apc36 q22 q23 q22 q25 q22).symm).trans (apc36 q23 q23 q22 q25 q22)).symm
  have apc40 : forall (q27 q28 q29 q30:G), ((q27 ◇ (q29 ◇ q27)) ◇ (q28 ◇ (q29 ◇ q28))) = (q30 ◇ ((q29 ◇ q29) ◇ q30)):=by
    intro q27 q28 q29 q30
    exact ((cg (fun t => t ◇ (q28 ◇ (q29 ◇ q28))) (apc9 q27 q29 q27 q27)).symm).trans (apc10 q28 q29 q30 (q29 ◇ q29))
  have apc43 : forall (q31 q32:G), (q32 ◇ ((q31 ◇ q31) ◇ q32)) = (q31 ◇ ((q31 ◇ q31) ◇ q31)):=by
    intro q31 q32
    exact ((apc40 q31 (q31 ◇ q31) q31 q32).symm).trans ((apc37 (q31 ◇ (q31 ◇ q31)) q31 q31 q31 q31).symm)
  have apc51 : forall (q33 q34 q35 q36:G), (((q33 ◇ (q34 ◇ q33)) ◇ q35) ◇ (q36 ◇ (q35 ◇ q36))) = (q34 ◇ q35):=by
    intro q33 q34 q35 q36
    exact ((cg (fun t => t ◇ (q36 ◇ (q35 ◇ q36))) (cg (fun t => t ◇ q35) (apc8 q33 q34 q35 q33))).symm).trans ((h (q34 ◇ q35) q35 q36).symm)
  have apc52 : forall (q37 q38:G), (q38 ◇ ((q38 ◇ (q38 ◇ q38)) ◇ q38)) = (q38 ◇ (q37 ◇ (q38 ◇ q37))):=by
    intro q37 q38
    exact ((((apc51 q37 q38 (q37 ◇ (q38 ◇ q37)) (q37 ◇ (q38 ◇ q37))).symm).trans (apc8 q37 (q37 ◇ (q38 ◇ q37)) ((q37 ◇ (q38 ◇ q37)) ◇ (q37 ◇ (q38 ◇ q37))) q37)).trans (apc25 q37 q38 q37)).symm
  have apc53 : forall (q39 q40:G), ((q40 ◇ (q40 ◇ q40)) ◇ q40) = (q39 ◇ (q40 ◇ q39)):=by
    intro q39 q40
    exact ((apc51 q40 (q40 ◇ (q40 ◇ q40)) q40 q39).symm).trans (((cg (fun t => t ◇ (q39 ◇ (q40 ◇ q39))) (cg (fun t => t ◇ q40) ((apc52 q39 q40).symm))).symm).trans ((h (q39 ◇ (q40 ◇ q39)) q40 q39).symm))
  have apc54 : forall (q41:G), (q41 ◇ (q41 ◇ (q41 ◇ q41))) = q41:=by
    intro q41
    exact (((cg (fun t => ((q41 ◇ (q41 ◇ q41)) ◇ (q41 ◇ (q41 ◇ q41))) ◇ t) (apc25 q41 q41 q41)).trans (apc51 q41 q41 (q41 ◇ (q41 ◇ q41)) q41)).symm).trans (((cg (fun t => t ◇ (q41 ◇ ((q41 ◇ (q41 ◇ q41)) ◇ q41))) (cg (fun t => t ◇ (q41 ◇ (q41 ◇ q41))) (apc53 q41 q41))).symm).trans ((h q41 (q41 ◇ (q41 ◇ q41)) q41).symm))
  have apc55 : forall (q42 q43:G), (q43 ◇ (q42 ◇ (q43 ◇ q42))) = q43:=by
    intro q42 q43
    exact ((cg (fun t => q43 ◇ t) (apc8 q42 q43 q43 q42)).symm).trans (apc54 q43)
  have apc56 : forall (q44 q45 q46:G), ((q44 ◇ (q46 ◇ q44)) ◇ q46) = (q45 ◇ (q46 ◇ q45)):=by
    intro q44 q45 q46
    exact ((cg (fun t => t ◇ q46) (apc8 q44 q46 q46 q44)).symm).trans (apc53 q45 q46)
  have apc57 : forall (q47:G), ((q47 ◇ q47) ◇ q47) = q47:=by
    intro q47
    exact ((cg (fun t => (q47 ◇ q47) ◇ t) (apc55 q47 q47)).symm).trans (((cg (fun t => (q47 ◇ q47) ◇ t) (cg (fun t => q47 ◇ t) (apc56 q47 q47 q47))).symm).trans (apc5 q47 q47 q47 q47 q47))
  have apc61 : forall (q31 q32 q47:G), (q32 ◇ ((q31 ◇ q31) ◇ q32)) = (q31 ◇ q31):=by
    intro q31 q32 q47
    exact (apc43 q31 q32).trans (cg (fun t => q31 ◇ t) (apc57 q31))
  have apc63 : forall (q48 q49:G), (q48 ◇ ((q48 ◇ (q49 ◇ q48)) ◇ q48)) = q49:=by
    intro q48 q49
    exact ((cg (fun t => q48 ◇ t) (apc12 q48 q49 q48 ((q48 ◇ (q49 ◇ q48)) ◇ q48))).symm).trans ((((apc8 q48 (q48 ◇ (q49 ◇ q48)) ((q48 ◇ (q49 ◇ q48)) ◇ (q48 ◇ (q49 ◇ q48))) q48).symm).trans (apc51 q48 q49 (q48 ◇ (q49 ◇ q48)) (q48 ◇ (q49 ◇ q48)))).trans (apc55 q48 q49))
  have apc64 : forall (q50 q51:G), ((q50 ◇ q50) ◇ q51) = q51:=by
    intro q50 q51
    exact (((apc23 q51 (q50 ◇ q50) ((q50 ◇ q50) ◇ q51)).trans (cg (fun t => t ◇ q51) (apc61 q50 q51 (q51 ◇ ((q50 ◇ q50) ◇ q51))))).symm).trans (((cg (fun t => ((q50 ◇ q50) ◇ q51) ◇ t) (cg (fun t => t ◇ ((q50 ◇ q50) ◇ q51)) (cg (fun t => ((q50 ◇ q50) ◇ q51) ◇ t) (apc61 q50 q51 q50)))).symm).trans (apc63 ((q50 ◇ q50) ◇ q51) q51))
  have apc83 : forall (q52 q53:G), (q53 ◇ (q53 ◇ (q52 ◇ q52))) = q53:=by
    intro q52 q53
    exact ((cg (fun t => q53 ◇ t) (apc64 q52 (q53 ◇ (q52 ◇ q52)))).symm).trans (apc55 (q52 ◇ q52) q53)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ y) ◇ x) ◇ (x ◇ (z ◇ z))):=((cg (fun t => t ◇ (x ◇ (z ◇ z))) (apc64 y x)).trans (apc83 z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23378_to_23474 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23378_to_23474
