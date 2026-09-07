-- Equation38190 → Equation52931
-- Recorded verdict: true
-- Premise: x = ((x * ((y * z) * z)) * z) * y
-- Conclusion: x * x = (((x * x) * x) * x) * y
-- Original submission SHA-256: 896f17eaf0d8777815ffd50785683beba9dcfda3e5251d55897e8dd6c51c35f7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ ((y ◇ z) ◇ z)) ◇ z) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (((x ◇ x) ◇ x) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ q2) ◇ (q0 ◇ ((q2 ◇ q2) ◇ q2))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q0 ◇ ((q2 ◇ q2) ◇ q2))) (cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) ((h q0 q2 q2).symm)))).symm).trans ((h q1 (q0 ◇ ((q2 ◇ q2) ◇ q2)) q2).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ (q4 ◇ ((q5 ◇ q5) ◇ q5))) = (q3 ◇ ((q5 ◇ q4) ◇ q4)):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ (q4 ◇ ((q5 ◇ q5) ◇ q5))) ((h q3 q5 q4).symm)).symm).trans (apc0 q4 (q3 ◇ ((q5 ◇ q4) ◇ q4)) q5)
  have apc2 : forall (q0 q1 q2 q3 q4 q5:G), (((q1 ◇ q0) ◇ q2) ◇ ((q2 ◇ q0) ◇ q0)) = q1:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc1 ((q1 ◇ q0) ◇ q2) q0 q2).symm).trans (apc0 q0 q1 q2)
  have apc4 : forall (q6 q7 q8 q9:G), ((q6 ◇ ((q8 ◇ q7) ◇ q7)) ◇ q7) = ((q6 ◇ q9) ◇ ((q9 ◇ q8) ◇ q8)):=by
    intro q6 q7 q8 q9
    exact (((cg (fun t => t ◇ ((q9 ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) ((h q6 q8 q7).symm))).symm).trans (apc2 q8 ((q6 ◇ ((q8 ◇ q7) ◇ q7)) ◇ q7) q9 q6 q6 q6)).symm
  have apc5 : forall (q10 q11 q12:G), (q11 ◇ ((((q12 ◇ q10) ◇ q10) ◇ q12) ◇ q12)) = (q11 ◇ q10):=by
    intro q10 q11 q12
    exact ((cg (fun t => t ◇ ((((q12 ◇ q10) ◇ q10) ◇ q12) ◇ q12)) (apc2 q10 q11 q12 q10 q10 q10)).symm).trans (apc2 q12 (q11 ◇ q10) ((q12 ◇ q10) ◇ q10) q10 q10 q10)
  have apc7 : forall (q6 q7 q8 q9:G), ((q6 ◇ q9) ◇ ((q9 ◇ q8) ◇ q8)) = ((q6 ◇ q6) ◇ ((q6 ◇ q8) ◇ q8)):=by
    intro q6 q7 q8 q9
    exact ((apc4 q6 q6 q8 q9).symm).trans (apc4 q6 q6 q8 q6)
  have apc17 : forall (q0 q13 q14 q2:G), ((q0 ◇ ((((q14 ◇ q2) ◇ q2) ◇ q13) ◇ q13)) ◇ q13) = ((q0 ◇ q2) ◇ q14):=by
    intro q0 q13 q14 q2
    exact (((cg (fun t => t ◇ q14) (cg (fun t => t ◇ q2) ((h q0 ((q14 ◇ q2) ◇ q2) q13).symm))).symm).trans ((h ((q0 ◇ ((((q14 ◇ q2) ◇ q2) ◇ q13) ◇ q13)) ◇ q13) q14 q2).symm)).symm
  have apc18 : forall (q6 q7 q8 q9:G), ((q6 ◇ ((q8 ◇ q7) ◇ q7)) ◇ q7) = ((q6 ◇ q6) ◇ ((q6 ◇ q8) ◇ q8)):=by
    intro q6 q7 q8 q9
    exact (apc4 q6 q7 q8 q6).trans (apc7 q6 ((q6 ◇ q6) ◇ ((q6 ◇ q8) ◇ q8)) q8 q6)
  have apc20 : forall (q15 q16 q17:G), (q16 ◇ ((((q15 ◇ q15) ◇ q15) ◇ q17) ◇ q17)) = (q16 ◇ ((q15 ◇ q17) ◇ q17)):=by
    intro q15 q16 q17
    exact ((((cg (fun t => q16 ◇ t) (apc1 q17 q15 q15)).trans (apc1 q16 q17 q15)).symm).trans (((cg (fun t => q16 ◇ t) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ ((q15 ◇ q15) ◇ q15)) (apc2 q15 q15 q15 q15 q15 q15)))).symm).trans (apc1 q16 q17 ((q15 ◇ q15) ◇ q15)))).symm
  have apc21 : forall (q18 q19:G), (q19 ◇ ((q18 ◇ q18) ◇ q18)) = (q19 ◇ q18):=by
    intro q18 q19
    exact ((apc20 q18 q19 q18).symm).trans (apc5 q18 q19 q18)
  have apc22 : forall (q20 q21:G), (q21 ◇ (q20 ◇ q20)) = (q21 ◇ q20):=by
    intro q20 q21
    exact ((cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q20) (apc2 q20 q20 q20 (((q20 ◇ q20) ◇ q20) ◇ ((q20 ◇ q20) ◇ q20)) (((q20 ◇ q20) ◇ q20) ◇ ((q20 ◇ q20) ◇ q20)) (((q20 ◇ q20) ◇ q20) ◇ ((q20 ◇ q20) ◇ q20))))).symm).trans ((((cg (fun t => q21 ◇ t) (apc21 q20 (((q20 ◇ q20) ◇ q20) ◇ ((q20 ◇ q20) ◇ q20)))).symm).trans (apc21 ((q20 ◇ q20) ◇ q20) q21)).trans (apc21 q20 q21))
  have apc23 : forall (q22 q23:G), (((q22 ◇ q23) ◇ q23) ◇ q23) = q22:=by
    intro q22 q23
    exact ((cg (fun t => t ◇ q23) (cg (fun t => t ◇ q23) (apc21 q23 q22))).symm).trans ((h q22 q23 q23).symm)
  have apc24 : forall (q3 q4 q5 q18 q19:G), (q3 ◇ ((q5 ◇ q4) ◇ q4)) = (q3 ◇ (q4 ◇ q5)):=by
    intro q3 q4 q5 q18 q19
    exact (((cg (fun t => q3 ◇ t) (apc21 q5 q4)).symm).trans (apc1 q3 q4 q5)).symm
  have apc25 : forall (q3 q4 q5 q18 q19 q10 q11 q12:G), (q11 ◇ (q12 ◇ (q10 ◇ q12))) = (q11 ◇ q10):=by
    intro q3 q4 q5 q18 q19 q10 q11 q12
    exact (((apc24 q11 q12 ((q12 ◇ q10) ◇ q10) (q11 ◇ ((((q12 ◇ q10) ◇ q10) ◇ q12) ◇ q12)) (q11 ◇ ((((q12 ◇ q10) ◇ q10) ◇ q12) ◇ q12))).trans (cg (fun t => q11 ◇ t) (apc24 q12 q10 q12 (q12 ◇ ((q12 ◇ q10) ◇ q10)) (q12 ◇ ((q12 ◇ q10) ◇ q10))))).symm).trans (apc5 q10 q11 q12)
  have apc26 : forall (q24 q25 q26:G), ((q24 ◇ (q26 ◇ q25)) ◇ q25) = ((q24 ◇ q25) ◇ q26):=by
    intro q24 q25 q26
    exact ((cg (fun t => t ◇ q25) (cg (fun t => q24 ◇ t) (apc23 (q26 ◇ q25) q25))).symm).trans (apc17 q24 q25 q26 q25)
  have apc27 : forall (q27 q28 q29:G), (q28 ◇ ((q27 ◇ q27) ◇ q29)) = (q28 ◇ (q27 ◇ q29)):=by
    intro q27 q28 q29
    exact ((((cg (fun t => q28 ◇ t) (cg (fun t => t ◇ q27) (apc22 q27 q29))).trans (apc24 q28 q27 q29 (q28 ◇ ((q29 ◇ q27) ◇ q27)) (q28 ◇ ((q29 ◇ q27) ◇ q27)))).symm).trans (((cg (fun t => q28 ◇ t) (apc22 q27 (q29 ◇ (q27 ◇ q27)))).symm).trans (apc24 q28 (q27 ◇ q27) q29 q27 q27))).symm
  have apc29 : forall (q30 q31 q32:G), (q32 ◇ ((q30 ◇ q31) ◇ q30)) = (q32 ◇ q31):=by
    intro q30 q31 q32
    exact ((cg (fun t => q32 ◇ t) (apc25 q30 q30 q30 q30 q30 q30 (q30 ◇ q31) q31)).symm).trans (apc25 q30 q30 q30 q30 q30 q31 q32 (q30 ◇ q31))
  have apc30 : forall (q33 q34 q35:G), (q35 ◇ (q34 ◇ q33)) = (q35 ◇ (q33 ◇ q34)):=by
    intro q33 q34 q35
    exact ((apc27 q34 q35 q33).symm).trans (((cg (fun t => q35 ◇ t) (apc26 q34 q34 q33)).symm).trans (apc29 q34 (q33 ◇ q34) q35))
  have apc31 : forall (q36 q37 q38:G), (q38 ◇ (q36 ◇ q37)) = (q38 ◇ q36):=by
    intro q36 q37 q38
    exact ((((cg (fun t => q38 ◇ t) (apc23 q36 q37)).symm).trans (apc30 q37 ((q36 ◇ q37) ◇ q37) q38)).trans (((((cg (fun t => q38 ◇ t) (apc24 q37 q37 q36 (q37 ◇ ((q36 ◇ q37) ◇ q37)) (q37 ◇ ((q36 ◇ q37) ◇ q37)))).trans (cg (fun t => q38 ◇ t) (apc30 q36 q37 q37))).trans (apc30 (q36 ◇ q37) q37 q38)).trans (apc24 q38 q37 q36 (q38 ◇ ((q36 ◇ q37) ◇ q37)) (q38 ◇ ((q36 ◇ q37) ◇ q37)))).trans (apc30 q36 q37 q38))).symm
  have apc32 : forall (q3 q4 q5 q18 q19 q36 q37 q38:G), (q3 ◇ q5) = (q3 ◇ q4):=by
    intro q3 q4 q5 q18 q19 q36 q37 q38
    exact (((apc31 (q5 ◇ q4) q4 q3).trans (apc31 q5 q4 q3)).symm).trans ((apc24 q3 q4 q5 q3 q3).trans (apc31 q4 q5 q3))
  have apc33 : forall (q3 q4 q5 q18 q19 q36 q37 q38:G), (q3 ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4 q5 q18 q19 q36 q37 q38
    exact ((apc32 q3 q4 q3 q3 q3 q3 q3 q3).symm).trans (apc32 q3 q3 q3 q3 q3 q3 q3 q3)
  have apc35 : forall (q3 q4 q5 q6 q7 q8 q9 q18 q19:G), ((q6 ◇ q6) ◇ (q6 ◇ q6)) = ((q6 ◇ q6) ◇ q7):=by
    intro q3 q4 q5 q6 q7 q8 q9 q18 q19
    exact ((((cg (fun t => t ◇ q7) (cg (fun t => q6 ◇ t) (apc33 q7 q8 (q7 ◇ q8) (q7 ◇ q8) (q7 ◇ q8) (q7 ◇ q8) (q7 ◇ q8) (q7 ◇ q8)))).trans (cg (fun t => t ◇ q7) (apc33 q6 (q7 ◇ q7) (q6 ◇ (q7 ◇ q7)) (q6 ◇ (q7 ◇ q7)) (q6 ◇ (q7 ◇ q7)) (q6 ◇ (q7 ◇ q7)) (q6 ◇ (q7 ◇ q7)) (q6 ◇ (q7 ◇ q7))))).symm).trans ((((cg (fun t => t ◇ q7) (apc24 q6 q7 q8 (q6 ◇ ((q8 ◇ q7) ◇ q7)) (q6 ◇ ((q8 ◇ q7) ◇ q7)))).symm).trans ((apc18 q6 q7 q8 q6).trans (apc24 (q6 ◇ q6) q8 q6 ((q6 ◇ q6) ◇ ((q6 ◇ q8) ◇ q8)) ((q6 ◇ q6) ◇ ((q6 ◇ q8) ◇ q8))))).trans (apc33 (q6 ◇ q6) (q8 ◇ q6) ((q6 ◇ q6) ◇ (q8 ◇ q6)) ((q6 ◇ q6) ◇ (q8 ◇ q6)) ((q6 ◇ q6) ◇ (q8 ◇ q6)) ((q6 ◇ q6) ◇ (q8 ◇ q6)) ((q6 ◇ q6) ◇ (q8 ◇ q6)) ((q6 ◇ q6) ◇ (q8 ◇ q6))))).symm
  have apc36 : forall (q3 q4 q5 q6 q7 q8 q9 q18 q19:G), ((q6 ◇ q6) ◇ q7) = ((q6 ◇ q6) ◇ q6):=by
    intro q3 q4 q5 q6 q7 q8 q9 q18 q19
    exact ((apc35 q6 q6 q6 q6 q7 q6 q6 q6 q6).symm).trans (apc35 q6 q6 q6 q6 q6 q6 q6 q6 q6)
  have apc38 : forall (q39 q40:G), (((q39 ◇ q39) ◇ q39) ◇ q40) = q39:=by
    intro q39 q40
    exact (((cg (fun t => t ◇ q40) (cg (fun t => t ◇ q40) (apc33 q39 ((q40 ◇ q40) ◇ q40) (q39 ◇ ((q40 ◇ q40) ◇ q40)) (q39 ◇ ((q40 ◇ q40) ◇ q40)) (q39 ◇ ((q40 ◇ q40) ◇ q40)) (q39 ◇ ((q40 ◇ q40) ◇ q40)) (q39 ◇ ((q40 ◇ q40) ◇ q40)) (q39 ◇ ((q40 ◇ q40) ◇ q40))))).trans (cg (fun t => t ◇ q40) (apc36 ((q39 ◇ q39) ◇ q40) ((q39 ◇ q39) ◇ q40) ((q39 ◇ q39) ◇ q40) q39 q40 ((q39 ◇ q39) ◇ q40) ((q39 ◇ q39) ◇ q40) ((q39 ◇ q39) ◇ q40) ((q39 ◇ q39) ◇ q40)))).symm).trans (((cg (fun t => t ◇ q40) (cg (fun t => t ◇ q40) (cg (fun t => q39 ◇ t) (apc36 q39 q39 q39 q40 q40 q39 q39 q39 q39)))).symm).trans ((h q39 q40 q40).symm))
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = ((((x ◇ x) ◇ x) ◇ x) ◇ y):=((cg (fun t => t ◇ y) (apc38 x x)).trans (apc33 x y (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38190_to_52931 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_38190_to_52931
