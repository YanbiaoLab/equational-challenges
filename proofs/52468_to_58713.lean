-- Equation52468 → Equation58713
-- Recorded verdict: true
-- Premise: x * y = ((y * (y * z)) * y) * x
-- Conclusion: (x * y) * z = x * (x * (w * u))
-- Original submission SHA-256: b1e27ee1735f30b801a723dc6c0d036c7643703869457e849b77d7e6af64af12
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ (y ◇ z)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = x ◇ (x ◇ (w ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), (((((q0 ◇ (q0 ◇ q1)) ◇ q0) ◇ (q3 ◇ q0)) ◇ ((q0 ◇ (q0 ◇ q1)) ◇ q0)) ◇ q2) = (q2 ◇ ((q0 ◇ (q0 ◇ q1)) ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q1)) ◇ q0)) (cg (fun t => ((q0 ◇ (q0 ◇ q1)) ◇ q0) ◇ t) ((h q3 q0 q1).symm)))).symm).trans ((h q2 ((q0 ◇ (q0 ◇ q1)) ◇ q0) q3).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((((q7 ◇ q4) ◇ q4) ◇ ((q4 ◇ (q4 ◇ q5)) ◇ q4)) ◇ q6) = (q6 ◇ ((q4 ◇ (q4 ◇ q5)) ◇ q4)):=by
    intro q4 q5 q6 q7
    exact ((cg (fun t => t ◇ q6) (cg (fun t => t ◇ ((q4 ◇ (q4 ◇ q5)) ◇ q4)) ((h (q7 ◇ q4) q4 q5).symm))).symm).trans (apc2 q4 q5 q6 q7)
  have apc6 : forall (q8 q9 q10 q11:G), ((((q9 ◇ q8) ◇ q9) ◇ ((q9 ◇ (q9 ◇ q10)) ◇ q9)) ◇ q11) = (q11 ◇ ((q9 ◇ (q9 ◇ q10)) ◇ q9)):=by
    intro q8 q9 q10 q11
    exact ((cg (fun t => t ◇ q11) (cg (fun t => t ◇ ((q9 ◇ (q9 ◇ q10)) ◇ q9)) (cg (fun t => t ◇ q9) ((h q9 q8 q8).symm)))).symm).trans (apc3 q9 q10 q11 ((q8 ◇ (q8 ◇ q8)) ◇ q8))
  have apc7 : forall (q12 q13 q14:G), ((((q12 ◇ (q12 ◇ q13)) ◇ q12) ◇ q12) ◇ q14) = (q14 ◇ ((q12 ◇ (q12 ◇ q13)) ◇ q12)):=by
    intro q12 q13 q14
    exact ((cg (fun t => t ◇ q14) ((h ((q12 ◇ (q12 ◇ q13)) ◇ q12) q12 q12).symm)).symm).trans (apc6 (q12 ◇ q12) q12 q13 q14)
  have apc8 : forall (q15 q16 q17:G), (q17 ◇ ((q15 ◇ (q15 ◇ q16)) ◇ q15)) = ((q15 ◇ q15) ◇ q17):=by
    intro q15 q16 q17
    exact (((cg (fun t => t ◇ q17) ((h q15 q15 q16).symm)).symm).trans (apc7 q15 q16 q17)).symm
  have apc9 : forall (q18 q19 q20:G), (q20 ◇ ((q19 ◇ ((q18 ◇ q18) ◇ q19)) ◇ q19)) = ((q19 ◇ q19) ◇ q20):=by
    intro q18 q19 q20
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q19) (cg (fun t => q19 ◇ t) (apc8 q18 q18 q19)))).symm).trans (apc8 q19 ((q18 ◇ (q18 ◇ q18)) ◇ q18) q20)
  have apc11 : forall (q21 q22 q23:G), (((q23 ◇ ((q21 ◇ q21) ◇ q23)) ◇ q23) ◇ q22) = (q22 ◇ q23):=by
    intro q21 q22 q23
    exact ((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc8 q21 q21 q23)))).symm).trans ((h q22 q23 ((q21 ◇ (q21 ◇ q21)) ◇ q21)).symm)
  have apc12 : forall (q24 q25 q26 q27:G), ((q24 ◇ q24) ◇ (q25 ◇ q25)) = (q24 ◇ q25):=by
    intro q24 q25 q26 q27
    exact (((apc11 q26 q24 q25).symm).trans ((((apc11 q27 ((q25 ◇ ((q26 ◇ q26) ◇ q25)) ◇ q25) q24).symm).trans (apc9 q26 q25 ((q24 ◇ ((q27 ◇ q27) ◇ q24)) ◇ q24))).trans (apc9 q27 q24 (q25 ◇ q25)))).symm
  have apc13 : forall (q28 q29:G), ((q28 ◇ q28) ◇ q29) = (q28 ◇ q29):=by
    intro q28 q29
    exact (((apc12 q28 q29 ((q28 ◇ q28) ◇ (q29 ◇ q29)) ((q28 ◇ q28) ◇ (q29 ◇ q29))).symm).trans (((cg (fun t => t ◇ (q29 ◇ q29)) (apc12 q28 q28 q28 q28)).symm).trans (apc12 (q28 ◇ q28) q29 q28 q28))).symm
  have apc16 : forall (q30 q31:G), ((q30 ◇ (q30 ◇ q30)) ◇ q31) = (q30 ◇ q31):=by
    intro q30 q31
    exact (((cg (fun t => t ◇ q31) (apc13 q30 (q30 ◇ q30))).symm).trans (apc13 (q30 ◇ q30) q31)).trans (apc13 q30 q31)
  have apc18 : forall (q32 q33:G), (q33 ◇ q32) = (q32 ◇ q33):=by
    intro q32 q33
    exact ((apc13 q33 q32).symm).trans (((cg (fun t => t ◇ q32) (apc16 q33 q33)).symm).trans ((h q32 q33 q33).symm))
  have apc20 : forall (q28 q29 q21 q22 q23:G), ((((q21 ◇ q23) ◇ q23) ◇ q23) ◇ q22) = (q22 ◇ q23):=by
    intro q28 q29 q21 q22 q23
    exact ((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (apc18 (q21 ◇ q23) q23))).symm).trans (((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc13 q21 q23)))).symm).trans (apc11 q21 q22 q23))
  have apc21 : forall (q34 q35 q36:G), ((((q35 ◇ q36) ◇ q35) ◇ q35) ◇ q34) = (q34 ◇ q35):=by
    intro q34 q35 q36
    exact (((cg (fun t => q34 ◇ t) (cg (fun t => t ◇ q35) (apc18 (q35 ◇ q36) q35))).trans (apc18 (((q35 ◇ q36) ◇ q35) ◇ q35) q34)).symm).trans (((apc18 q34 ((q35 ◇ (q35 ◇ q36)) ◇ q35)).symm).trans ((h q34 q35 q36).symm))
  have apc22 : forall (q37 q38 q39:G), (((q37 ◇ q39) ◇ q39) ◇ q38) = (q38 ◇ q39):=by
    intro q37 q38 q39
    exact ((((((((cg (fun t => t ◇ q38) (cg (fun t => t ◇ (q39 ◇ (q39 ◇ q37))) (cg (fun t => t ◇ q39) (cg (fun t => q39 ◇ t) (apc18 q37 q39))))).trans (cg (fun t => t ◇ q38) (cg (fun t => ((q39 ◇ (q37 ◇ q39)) ◇ q39) ◇ t) (cg (fun t => q39 ◇ t) (apc18 q37 q39))))).trans (cg (fun t => t ◇ q38) (cg (fun t => t ◇ (q39 ◇ (q37 ◇ q39))) (cg (fun t => t ◇ q39) (apc18 (q37 ◇ q39) q39))))).trans (cg (fun t => t ◇ q38) (cg (fun t => (((q37 ◇ q39) ◇ q39) ◇ q39) ◇ t) (apc18 (q37 ◇ q39) q39)))).trans (cg (fun t => t ◇ q38) (apc20 ((((q37 ◇ q39) ◇ q39) ◇ q39) ◇ ((q37 ◇ q39) ◇ q39)) ((((q37 ◇ q39) ◇ q39) ◇ q39) ◇ ((q37 ◇ q39) ◇ q39)) q37 ((q37 ◇ q39) ◇ q39) q39))).trans (apc20 ((((q37 ◇ q39) ◇ q39) ◇ q39) ◇ q38) ((((q37 ◇ q39) ◇ q39) ◇ q39) ◇ q38) q37 q38 q39)).symm).trans ((((cg (fun t => t ◇ q38) (cg (fun t => t ◇ (q39 ◇ (q39 ◇ q37))) ((h (q39 ◇ (q39 ◇ q37)) q39 q37).symm))).symm).trans (apc21 q38 (q39 ◇ (q39 ◇ q37)) q39)).trans (((cg (fun t => q38 ◇ t) (cg (fun t => q39 ◇ t) (apc18 q37 q39))).trans (cg (fun t => q38 ◇ t) (apc18 (q37 ◇ q39) q39))).trans (apc18 ((q37 ◇ q39) ◇ q39) q38)))).symm
  have apc23 : forall (q40 q41 q42:G), ((((q40 ◇ q41) ◇ q40) ◇ (q40 ◇ q40)) ◇ q42) = (q40 ◇ q42):=by
    intro q40 q41 q42
    exact ((((cg (fun t => q42 ◇ t) (cg (fun t => t ◇ (q40 ◇ q40)) (apc13 q40 (q40 ◇ q41)))).trans (cg (fun t => q42 ◇ t) (cg (fun t => t ◇ (q40 ◇ q40)) (apc18 (q40 ◇ q41) q40)))).trans (apc18 (((q40 ◇ q41) ◇ q40) ◇ (q40 ◇ q40)) q42)).symm).trans ((((cg (fun t => q42 ◇ t) (cg (fun t => t ◇ (q40 ◇ q40)) (cg (fun t => (q40 ◇ q40) ◇ t) (apc12 q40 q41 q40 q40)))).symm).trans (apc8 (q40 ◇ q40) (q41 ◇ q41) q42)).trans ((((cg (fun t => t ◇ q42) (apc13 q40 (q40 ◇ q40))).trans (cg (fun t => t ◇ q42) (apc18 (q40 ◇ q40) q40))).trans (cg (fun t => t ◇ q42) (apc13 q40 q40))).trans (apc13 q40 q42)))
  have apc24 : forall (q43 q44 q45:G), ((q43 ◇ q44) ◇ q45) = (q44 ◇ q45):=by
    intro q43 q44 q45
    exact ((((((((cg (fun t => t ◇ q45) (apc18 ((q43 ◇ q44) ◇ (q43 ◇ q44)) ((q43 ◇ q44) ◇ q44))).trans (cg (fun t => t ◇ q45) (apc13 (q43 ◇ q44) ((q43 ◇ q44) ◇ q44)))).trans (cg (fun t => t ◇ q45) (apc18 ((q43 ◇ q44) ◇ q44) (q43 ◇ q44)))).trans (cg (fun t => t ◇ q45) (apc22 q43 (q43 ◇ q44) q44))).trans (apc22 q43 q45 q44)).trans (apc18 q44 q45)).symm).trans (((cg (fun t => t ◇ q45) (cg (fun t => t ◇ ((q43 ◇ q44) ◇ (q43 ◇ q44))) (apc22 q43 (q43 ◇ q44) q44))).symm).trans (apc23 (q43 ◇ q44) q44 q45))).symm
  have apc25 : forall (q46 q47 q48:G), (q46 ◇ q48) = (q46 ◇ q47):=by
    intro q46 q47 q48
    exact (((((cg (fun t => t ◇ q46) (apc24 q47 q48 q47)).trans (cg (fun t => t ◇ q46) (apc18 q47 q48))).trans (apc24 q47 q48 q46)).trans (apc18 q46 q48)).symm).trans (((cg (fun t => t ◇ q46) (apc24 q47 (q47 ◇ q48) q47)).symm).trans ((h q46 q47 q48).symm))
  have apc27 : forall (q46 q47 q48:G), (q46 ◇ q47) = (q46 ◇ q46):=by
    intro q46 q47 q48
    exact ((apc25 q46 q47 q48).symm).trans (apc25 q46 q46 q48)
  have apc30 : forall (q49 q50 q51 q52:G), ((q50 ◇ q49) ◇ q52) = (q51 ◇ q51):=by
    intro q49 q50 q51 q52
    exact (((cg (fun t => t ◇ q52) (apc25 q50 q49 q51)).symm).trans (apc24 q50 q51 q52)).trans (apc27 q51 q52 (q51 ◇ q52))
  have apc34 : forall (q53 q54 q55:G), (q55 ◇ q53) = (q54 ◇ q54):=by
    intro q53 q54 q55
    exact (h q55 q53 q53).trans (apc30 q53 (q53 ◇ (q53 ◇ q53)) q54 q55)
  exact (apc34 z ((x ◇ y) ◇ z) (x ◇ y)).trans ((apc34 (x ◇ (w ◇ u)) ((x ◇ y) ◇ z) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52468_to_58713 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52468_to_58713
