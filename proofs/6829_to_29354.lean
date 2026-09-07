-- Equation6829 → Equation29354
-- Recorded verdict: true
-- Premise: x = y ◇ (y ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x = (x ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ y
-- Original submission SHA-256: 2d4c248d55083cdf72b5ff0ac96e1b2d43777ae72f8235f1ab61bb9365c9b888
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((x ◇ z) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), (q3 ◇ (q3 ◇ (q0 ◇ (q3 ◇ (q2 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) ((h q0 q2 q1).symm)))).symm).trans ((h q2 q3 (q2 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))).symm)
  have apc3 : forall (q4 q5:G), (q5 ◇ (q5 ◇ (q4 ◇ q4))) = q5:=by
    intro q4 q5
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => q4 ◇ t) ((h q4 q5 q4).symm)))).symm).trans (apc2 q4 q4 q5 q5)
  have apc4 : forall (q6:G), ((q6 ◇ q6) ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q6
    exact ((cg (fun t => (q6 ◇ q6) ◇ t) (apc3 q6 (q6 ◇ q6))).symm).trans (apc3 (q6 ◇ q6) (q6 ◇ q6))
  have apc5 : forall (q7 q8 q9:G), (q9 ◇ (q9 ◇ (q8 ◇ (q9 ◇ (q8 ◇ (q7 ◇ q7)))))) = q8:=by
    intro q7 q8 q9
    exact ((cg (fun t => q9 ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => t ◇ (q9 ◇ (q8 ◇ (q7 ◇ q7)))) (apc3 q7 q8)))).symm).trans ((h q8 q9 (q8 ◇ (q7 ◇ q7))).symm)
  have apc6 : forall (q10 q11:G), ((q10 ◇ (q11 ◇ q11)) ◇ q10) = (q10 ◇ (q11 ◇ q11)):=by
    intro q10 q11
    exact ((cg (fun t => (q10 ◇ (q11 ◇ q11)) ◇ t) ((h q10 (q10 ◇ (q11 ◇ q11)) (q11 ◇ q11)).symm)).symm).trans (apc5 q11 (q10 ◇ (q11 ◇ q11)) (q10 ◇ (q11 ◇ q11)))
  have apc7 : forall (q7 q8 q9:G), (q9 ◇ (q9 ◇ ((q8 ◇ (q9 ◇ (q7 ◇ q7))) ◇ q9))) = q8:=by
    intro q7 q8 q9
    exact ((cg (fun t => q9 ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => (q8 ◇ (q9 ◇ (q7 ◇ q7))) ◇ t) (apc3 q7 q9)))).symm).trans ((h q8 q9 (q9 ◇ (q7 ◇ q7))).symm)
  have apc10 : forall (q12 q13 q14:G), (q13 ◇ (q13 ◇ ((q14 ◇ (q12 ◇ q12)) ◇ (q13 ◇ q14)))) = (q14 ◇ (q12 ◇ q12)):=by
    intro q12 q13 q14
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => q13 ◇ t) (cg (fun t => t ◇ (q13 ◇ q14)) (apc6 q14 q12)))).symm).trans ((h (q14 ◇ (q12 ◇ q12)) q13 q14).symm)
  have apc11 : forall (q15 q16:G), ((q15 ◇ q15) ◇ (q16 ◇ q16)) = (q15 ◇ q15):=by
    intro q15 q16
    exact (((((cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => (q15 ◇ q15) ◇ t) (apc6 (q15 ◇ q15) q16))).trans (cg (fun t => (q15 ◇ q15) ◇ t) (apc3 q16 (q15 ◇ q15)))).trans (apc4 q15)).symm).trans (((cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => ((q15 ◇ q15) ◇ (q16 ◇ q16)) ◇ t) (apc4 q15)))).symm).trans (apc10 q16 (q15 ◇ q15) (q15 ◇ q15)))).symm
  have apc12 : forall (q17 q18:G), (q18 ◇ q18) = (q17 ◇ q17):=by
    intro q17 q18
    exact (((((cg (fun t => (q17 ◇ q17) ◇ t) (cg (fun t => (q17 ◇ q17) ◇ t) (apc11 q18 q17))).trans (cg (fun t => (q17 ◇ q17) ◇ t) (apc11 q17 q18))).trans (apc11 q17 q17)).symm).trans (((cg (fun t => (q17 ◇ q17) ◇ t) (cg (fun t => (q17 ◇ q17) ◇ t) (cg (fun t => (q18 ◇ q18) ◇ t) (apc11 q17 (q18 ◇ q18))))).symm).trans (apc5 q18 (q18 ◇ q18) (q17 ◇ q17)))).symm
  have apc15 : forall (q19 q20 q21:G), (q21 ◇ (q21 ◇ ((q19 ◇ q19) ◇ q21))) = (q21 ◇ (q20 ◇ q20)):=by
    intro q19 q20 q21
    exact ((cg (fun t => q21 ◇ t) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q21) (apc12 q19 (q21 ◇ (q20 ◇ q20)))))).symm).trans (apc7 q20 (q21 ◇ (q20 ◇ q20)) q21)
  have apc16 : forall (q22 q23 q24:G), (q24 ◇ (((q22 ◇ q22) ◇ q23) ◇ (q24 ◇ q23))) = q24:=by
    intro q22 q23 q24
    exact ((apc3 q22 (q24 ◇ (((q22 ◇ q22) ◇ q23) ◇ (q24 ◇ q23)))).symm).trans (((cg (fun t => (q24 ◇ (((q22 ◇ q22) ◇ q23) ◇ (q24 ◇ q23))) ◇ t) (cg (fun t => (q24 ◇ (((q22 ◇ q22) ◇ q23) ◇ (q24 ◇ q23))) ◇ t) (apc11 q22 (q24 ◇ (((q22 ◇ q22) ◇ q23) ◇ (q24 ◇ q23)))))).symm).trans (apc2 (q22 ◇ q22) q23 q24 (q24 ◇ (((q22 ◇ q22) ◇ q23) ◇ (q24 ◇ q23)))))
  have apc17 : forall (q25 q26:G), ((q25 ◇ q25) ◇ ((q25 ◇ q25) ◇ q26)) = q26:=by
    intro q25 q26
    exact (((cg (fun t => ((q25 ◇ q25) ◇ (q25 ◇ q25)) ◇ t) (cg (fun t => t ◇ q26) (apc11 q25 q25))).trans (cg (fun t => t ◇ ((q25 ◇ q25) ◇ q26)) (apc11 q25 q25))).symm).trans (((cg (fun t => ((q25 ◇ q25) ◇ (q25 ◇ q25)) ◇ t) (cg (fun t => ((q25 ◇ q25) ◇ (q25 ◇ q25)) ◇ t) (apc16 q25 (q25 ◇ q25) q26))).symm).trans (apc5 q25 q26 ((q25 ◇ q25) ◇ (q25 ◇ q25))))
  have apc21 : forall (q27 q28 q29:G), ((q28 ◇ q29) ◇ ((q27 ◇ q27) ◇ q29)) = q28:=by
    intro q27 q28 q29
    exact ((apc17 q27 ((q28 ◇ q29) ◇ ((q27 ◇ q27) ◇ q29))).symm).trans ((h q28 (q27 ◇ q27) q29).symm)
  have apc31 : forall (q30 q31 q32:G), (q31 ◇ (q31 ◇ ((q30 ◇ q30) ◇ (q31 ◇ q32)))) = q32:=by
    intro q30 q31 q32
    exact ((cg (fun t => q31 ◇ t) (cg (fun t => q31 ◇ t) (cg (fun t => t ◇ (q31 ◇ q32)) (apc12 q30 q32)))).symm).trans ((h q32 q31 q32).symm)
  have apc32 : forall (q33 q34 q35:G), (q35 ◇ ((q33 ◇ q33) ◇ q35)) = (q34 ◇ q34):=by
    intro q33 q34 q35
    exact (((apc31 q33 q35 (q34 ◇ q34)).symm).trans (((cg (fun t => q35 ◇ t) (cg (fun t => q35 ◇ t) (cg (fun t => (q33 ◇ q33) ◇ t) (apc15 q33 q34 q35)))).symm).trans (apc31 q33 q35 (q35 ◇ ((q33 ◇ q33) ◇ q35))))).symm
  have apc33 : forall (q36 q37:G), ((q36 ◇ q36) ◇ q37) = q37:=by
    intro q36 q37
    exact ((apc31 q36 q36 ((q36 ◇ q36) ◇ q37)).symm).trans (((cg (fun t => q36 ◇ t) (cg (fun t => q36 ◇ t) (cg (fun t => t ◇ (q36 ◇ ((q36 ◇ q36) ◇ q37))) (apc32 q36 q36 q37)))).symm).trans ((h q37 q36 ((q36 ◇ q36) ◇ q37)).symm))
  have apc34 : forall (q27 q28 q29 q36 q37:G), ((q28 ◇ q29) ◇ q29) = q28:=by
    intro q27 q28 q29 q36 q37
    exact ((cg (fun t => (q28 ◇ q29) ◇ t) (apc33 q28 q29)).symm).trans (apc21 q28 q28 q29)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ y):=((cg (fun t => t ◇ y) (cg (fun t => x ◇ t) (apc3 y y))).trans (apc34 ((x ◇ y) ◇ y) x y ((x ◇ y) ◇ y) ((x ◇ y) ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6829_to_29354 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6829_to_29354
