-- Equation40359 → Equation42405
-- Recorded verdict: true
-- Premise: x = (((y * (z * y)) * x) * x) * z
-- Conclusion: x * y = z * (w * (u * (v * r)))
-- Original submission SHA-256: 361fe2b8a429afa2fd4c3b29120c6ae9baf0fca83edcdfa97ced96b6a8f11ce6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ (z ◇ y)) ◇ x) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G) (r : G), x ◇ y = z ◇ (w ◇ (u ◇ (v ◇ r)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v r
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), ((((q3 ◇ q0) ◇ q2) ◇ q2) ◇ (((q1 ◇ (q3 ◇ q1)) ◇ q0) ◇ q0)) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (((q1 ◇ (q3 ◇ q1)) ◇ q0) ◇ q0)) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q2) (cg (fun t => q3 ◇ t) ((h q0 q1 q3).symm))))).symm).trans ((h q2 q3 (((q1 ◇ (q3 ◇ q1)) ◇ q0) ◇ q0)).symm)
  have apc3 : forall (q4 q5 q6:G), (q6 ◇ (((q5 ◇ ((q4 ◇ (q6 ◇ q4)) ◇ q5)) ◇ q6) ◇ q6)) = q6:=by
    intro q4 q5 q6
    exact ((cg (fun t => t ◇ (((q5 ◇ ((q4 ◇ (q6 ◇ q4)) ◇ q5)) ◇ q6) ◇ q6)) ((h q6 q4 q6).symm)).symm).trans (apc2 q6 q5 q6 (q4 ◇ (q6 ◇ q4)))
  have apc4 : forall (q7 q8 q9 q10:G), (((q10 ◇ q9) ◇ q9) ◇ ((q8 ◇ ((q7 ◇ (q10 ◇ q7)) ◇ q8)) ◇ q10)) = q9:=by
    intro q7 q8 q9 q10
    exact ((cg (fun t => t ◇ ((q8 ◇ ((q7 ◇ (q10 ◇ q7)) ◇ q8)) ◇ q10)) (cg (fun t => t ◇ q9) (cg (fun t => t ◇ q9) (apc3 q7 q8 q10)))).symm).trans ((h q9 q10 ((q8 ◇ ((q7 ◇ (q10 ◇ q7)) ◇ q8)) ◇ q10)).symm)
  have apc5 : forall (q11 q12 q13 q14 q15:G), (q15 ◇ ((q14 ◇ ((q13 ◇ (q15 ◇ q13)) ◇ q14)) ◇ q15)) = (((q12 ◇ ((q11 ◇ (q15 ◇ q11)) ◇ q12)) ◇ q15) ◇ q15):=by
    intro q11 q12 q13 q14 q15
    exact ((cg (fun t => t ◇ ((q14 ◇ ((q13 ◇ (q15 ◇ q13)) ◇ q14)) ◇ q15)) (apc3 q11 q12 q15)).symm).trans (((cg (fun t => t ◇ ((q14 ◇ ((q13 ◇ (q15 ◇ q13)) ◇ q14)) ◇ q15)) (cg (fun t => t ◇ (((q12 ◇ ((q11 ◇ (q15 ◇ q11)) ◇ q12)) ◇ q15) ◇ q15)) (apc3 q11 q12 q15))).symm).trans (apc4 q13 q14 (((q12 ◇ ((q11 ◇ (q15 ◇ q11)) ◇ q12)) ◇ q15) ◇ q15) q15))
  have apc8 : forall (q11 q12 q13 q14 q15:G), (q15 ◇ ((q14 ◇ ((q13 ◇ (q15 ◇ q13)) ◇ q14)) ◇ q15)) = (q15 ◇ ((q11 ◇ ((q11 ◇ (q15 ◇ q11)) ◇ q11)) ◇ q15)):=by
    intro q11 q12 q13 q14 q15
    exact (apc5 q11 q11 q13 q14 q15).trans ((apc5 q11 q11 q11 q11 q15).symm)
  have apc15 : forall (q4 q16 q5 q6:G), ((q16 ◇ q6) ◇ (((q5 ◇ (((q4 ◇ (q6 ◇ q4)) ◇ q16) ◇ q5)) ◇ q16) ◇ q16)) = q6:=by
    intro q4 q16 q5 q6
    exact ((cg (fun t => t ◇ (((q5 ◇ (((q4 ◇ (q6 ◇ q4)) ◇ q16) ◇ q5)) ◇ q16) ◇ q16)) (cg (fun t => t ◇ q6) ((h q16 q4 q6).symm))).symm).trans (apc2 q16 q5 q6 ((q4 ◇ (q6 ◇ q4)) ◇ q16))
  have apc16 : forall (q17 q18:G), ((q18 ◇ (q17 ◇ (q18 ◇ q17))) ◇ ((q18 ◇ q18) ◇ q18)) = (q17 ◇ (q18 ◇ q17)):=by
    intro q17 q18
    exact ((cg (fun t => (q18 ◇ (q17 ◇ (q18 ◇ q17))) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ q18) (apc3 q17 q17 q18)))).symm).trans (apc15 q17 q18 q18 (q17 ◇ (q18 ◇ q17)))
  have apc18 : forall (q19 q20 q21 q22:G), ((q22 ◇ ((q21 ◇ ((q20 ◇ (q22 ◇ q20)) ◇ q21)) ◇ q22)) ◇ (q19 ◇ (q22 ◇ q19))) = q22:=by
    intro q19 q20 q21 q22
    exact ((cg (fun t => t ◇ (q19 ◇ (q22 ◇ q19))) ((apc5 q19 q19 q20 q21 q22).symm)).symm).trans ((h q22 q19 (q19 ◇ (q22 ◇ q19))).symm)
  have apc19 : forall (q23 q24:G), ((q23 ◇ (q24 ◇ q23)) ◇ (q24 ◇ (q23 ◇ (q24 ◇ q23)))) = (q23 ◇ (q24 ◇ q23)):=by
    intro q23 q24
    exact ((cg (fun t => (q23 ◇ (q24 ◇ q23)) ◇ t) (cg (fun t => t ◇ (q23 ◇ (q24 ◇ q23))) (apc18 q23 q23 q23 q24))).symm).trans (apc3 q23 q24 (q23 ◇ (q24 ◇ q23)))
  have apc59 : forall (q25 q26 q27:G), (((q25 ◇ (q27 ◇ q25)) ◇ q27) ◇ (q26 ◇ ((q25 ◇ (q27 ◇ q25)) ◇ q26))) = (q25 ◇ (q27 ◇ q25)):=by
    intro q25 q26 q27
    exact ((cg (fun t => t ◇ (q26 ◇ ((q25 ◇ (q27 ◇ q25)) ◇ q26))) (cg (fun t => (q25 ◇ (q27 ◇ q25)) ◇ t) (apc18 q25 q25 q25 q27))).symm).trans (((cg (fun t => t ◇ (q26 ◇ ((q25 ◇ (q27 ◇ q25)) ◇ q26))) (cg (fun t => (q25 ◇ (q27 ◇ q25)) ◇ t) (cg (fun t => t ◇ (q25 ◇ (q27 ◇ q25))) (apc8 q25 q25 q25 q25 q27)))).symm).trans (apc18 q26 q25 q27 (q25 ◇ (q27 ◇ q25))))
  have apc108 : forall (q28 q29 q30 q31 q32:G), (((((((q29 ◇ (q31 ◇ q29)) ◇ q28) ◇ q28) ◇ q30) ◇ q32) ◇ q32) ◇ (((q31 ◇ q28) ◇ q30) ◇ q30)) = q32:=by
    intro q28 q29 q30 q31 q32
    exact ((cg (fun t => t ◇ (((q31 ◇ q28) ◇ q30) ◇ q30)) (cg (fun t => t ◇ q32) (cg (fun t => t ◇ q32) (cg (fun t => (((q29 ◇ (q31 ◇ q29)) ◇ q28) ◇ q28) ◇ t) (apc2 q28 q29 q30 q31))))).symm).trans ((h q32 (((q29 ◇ (q31 ◇ q29)) ◇ q28) ◇ q28) (((q31 ◇ q28) ◇ q30) ◇ q30)).symm)
  have apc109 : forall (q33 q34 q35:G), (((q33 ◇ q35) ◇ q35) ◇ (((q34 ◇ q33) ◇ q34) ◇ q34)) = q35:=by
    intro q33 q34 q35
    exact ((cg (fun t => t ◇ (((q34 ◇ q33) ◇ q34) ◇ q34)) (cg (fun t => t ◇ q35) (cg (fun t => t ◇ q35) ((h q33 q33 q34).symm)))).symm).trans (apc108 q33 q33 q34 q34 q35)
  have apc114 : forall (q36 q37 q38:G), (((((q37 ◇ q37) ◇ q37) ◇ q38) ◇ q38) ◇ (q36 ◇ (q37 ◇ q36))) = q38:=by
    intro q36 q37 q38
    exact (((cg (fun t => ((((q37 ◇ q37) ◇ q37) ◇ q38) ◇ q38) ◇ t) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ (q37 ◇ q36)))) (apc19 q36 q37))).trans (cg (fun t => ((((q37 ◇ q37) ◇ q37) ◇ q38) ◇ q38) ◇ t) (apc19 q36 q37))).symm).trans (((cg (fun t => ((((q37 ◇ q37) ◇ q37) ◇ q38) ◇ q38) ◇ t) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ (q37 ◇ q36)))) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ (q37 ◇ q36)))) (apc16 q36 q37)))).symm).trans (apc109 ((q37 ◇ q37) ◇ q37) (q37 ◇ (q36 ◇ (q37 ◇ q36))) q38))
  have apc115 : forall (q39 q40:G), (q39 ◇ (q40 ◇ q39)) = q40:=by
    intro q39 q40
    exact ((apc59 q39 q39 q40).symm).trans (((cg (fun t => t ◇ (q39 ◇ ((q39 ◇ (q40 ◇ q39)) ◇ q39))) (cg (fun t => t ◇ q40) ((h (q39 ◇ (q40 ◇ q39)) q39 q40).symm))).symm).trans (apc114 q39 (q39 ◇ (q40 ◇ q39)) q40))
  have apc117 : forall (q41 q42:G), ((q41 ◇ q42) ◇ q41) = q42:=by
    intro q41 q42
    exact ((cg (fun t => (q41 ◇ q42) ◇ t) (apc115 q42 q41)).symm).trans (apc115 (q41 ◇ q42) q42)
  have apc118 : forall (q43 q44:G), (q44 ◇ q43) = q44:=by
    intro q43 q44
    exact (((cg (fun t => q43 ◇ t) (cg (fun t => t ◇ q43) (cg (fun t => t ◇ q43) (apc115 q43 q44)))).trans (apc115 q43 (q44 ◇ q43))).symm).trans (((cg (fun t => t ◇ (((q43 ◇ (q44 ◇ q43)) ◇ q43) ◇ q43)) ((h q43 q43 q44).symm)).symm).trans (apc117 (((q43 ◇ (q44 ◇ q43)) ◇ q43) ◇ q43) q44))
  have apc119 : forall (x y z q43 q44:G), y = x:=by
    intro x y z q43 q44
    exact ((h x y x).trans (((((cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => y ◇ t) (apc118 y x))))).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc118 x y))))).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc118 x y)))).trans (cg (fun t => t ◇ x) (apc118 x y))).trans (apc118 x y))).symm
  exact (apc119 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc119 (x ◇ y) (z ◇ (w ◇ (u ◇ (v ◇ r)))) (x ◇ y) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40359_to_42405 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40359_to_42405
