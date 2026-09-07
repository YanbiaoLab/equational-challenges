-- Equation45536 → Equation57846
-- Recorded verdict: true
-- Premise: x * y = y * (((z * w) * u) * x)
-- Conclusion: x * (y * z) = ((x * y) * z) * y
-- Original submission SHA-256: fed71d362c74d7bc7ce3fdc98a3d5600573afc590a8bc50af193bb1b9da9144f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ (((z ◇ w) ◇ u) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = ((x ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ ((q0 ◇ (q4 ◇ q1)) ◇ q2)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q2) ((h q0 (q4 ◇ q1) q0 q0 q0).symm))).symm).trans ((h q2 q3 q4 q1 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q8 ◇ ((q6 ◇ q5) ◇ q7)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q7) ((h q6 q5 q5 q5 q5).symm))).symm).trans (apc0 q5 q6 q7 q8 ((q5 ◇ q5) ◇ q5))
  have apc2 : forall (q9 q10 q11 q12 q13 q14 q15:G), (((q10 ◇ q9) ◇ q11) ◇ q13) = (q13 ◇ (q12 ◇ q11)):=by
    intro q9 q10 q11 q12 q13 q14 q15
    exact (((cg (fun t => q13 ◇ t) (apc1 q14 q15 q12 q11)).symm).trans (((cg (fun t => q13 ◇ t) (apc1 q9 q10 q11 ((q15 ◇ q14) ◇ q12))).symm).trans ((h ((q10 ◇ q9) ◇ q11) q13 q15 q14 q12).symm))).symm
  have apc3 : forall (q16 q17 q18 q19:G), (((q17 ◇ q16) ◇ q18) ◇ q19) = (q18 ◇ q19):=by
    intro q16 q17 q18 q19
    exact (apc2 q16 q17 q18 (q16 ◇ q16) q19 q16 q16).trans (apc1 q16 q16 q18 q19)
  have apc5 : forall (x y z w u:G), (y ◇ (x ◇ x)) = (y ◇ (u ◇ x)):=by
    intro x y z w u
    exact (((cg (fun t => y ◇ t) (apc3 w z u x)).symm).trans ((((h x y z w u).symm).trans (h x y x x x)).trans (cg (fun t => y ◇ t) (apc3 x x x x)))).symm
  have apc13 : forall (q20 q21:G), (q21 ◇ (q20 ◇ q20)) = (q20 ◇ q21):=by
    intro q20 q21
    exact (apc5 q20 q21 q20 q20 (q20 ◇ q20)).trans (apc1 q20 q20 q20 q21)
  have apc14 : forall (q22 q23 q24 q25 q26:G), (q24 ◇ (q23 ◇ q22)) = ((q22 ◇ q22) ◇ q24):=by
    intro q22 q23 q24 q25 q26
    exact ((cg (fun t => q24 ◇ t) (apc1 q25 q26 q23 q22)).symm).trans (((cg (fun t => q24 ◇ t) (apc13 q22 ((q26 ◇ q25) ◇ q23))).symm).trans ((h (q22 ◇ q22) q24 q26 q25 q23).symm))
  have apc15 : forall (q9 q10 q11 q12 q14 q13 q15 q16 q17 q18 q19:G), ((q11 ◇ q11) ◇ q13) = (q11 ◇ q13):=by
    intro q9 q10 q11 q12 q14 q13 q15 q16 q17 q18 q19
    exact ((((apc3 q9 q10 q11 q13).symm).trans (apc2 q9 q10 q11 q12 q13 q14 q15)).trans (apc14 q11 q12 q13 (q13 ◇ (q12 ◇ q11)) (q13 ◇ (q12 ◇ q11)))).symm
  have apc16 : forall (q22 q23 q25 q24 q26 q9 q10 q11 q12 q14 q13 q15 q16 q17 q18 q19:G), (q24 ◇ (q23 ◇ q22)) = (q22 ◇ q24):=by
    intro q22 q23 q25 q24 q26 q9 q10 q11 q12 q14 q13 q15 q16 q17 q18 q19
    exact (apc14 q22 q23 q24 q25 q26).trans (apc15 ((q22 ◇ q22) ◇ q24) ((q22 ◇ q22) ◇ q24) q22 ((q22 ◇ q22) ◇ q24) ((q22 ◇ q22) ◇ q24) q24 ((q22 ◇ q22) ◇ q24) ((q22 ◇ q22) ◇ q24) ((q22 ◇ q22) ◇ q24) ((q22 ◇ q22) ◇ q24) ((q22 ◇ q22) ◇ q24))
  have apc17 : forall (q27 q28 q29:G), ((q27 ◇ q28) ◇ q29) = (q28 ◇ q29):=by
    intro q27 q28 q29
    exact ((cg (fun t => t ◇ q29) (apc3 q27 q27 q27 q28)).symm).trans (apc3 q27 (q27 ◇ q27) q28 q29)
  have apc19 : forall (q30 q18 q31 q32 q33 q16 q17:G), (q18 ◇ q30) = (q30 ◇ q18):=by
    intro q30 q18 q31 q32 q33 q16 q17
    exact ((((cg (fun t => t ◇ (q31 ◇ q30)) (apc17 q32 q33 q18)).trans (apc16 q30 q31 ((q33 ◇ q18) ◇ (q31 ◇ q30)) (q33 ◇ q18) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)) ((q33 ◇ q18) ◇ (q31 ◇ q30)))).trans (apc16 q18 q33 (q30 ◇ (q33 ◇ q18)) q30 (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)) (q30 ◇ (q33 ◇ q18)))).symm).trans ((((apc2 q16 q17 q30 q31 ((q32 ◇ q33) ◇ q18) q16 q16).symm).trans (apc1 q33 q32 q18 ((q17 ◇ q16) ◇ q30))).trans ((cg (fun t => q18 ◇ t) (apc17 q17 q16 q30)).trans (apc16 q30 q16 (q18 ◇ (q16 ◇ q30)) q18 (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)) (q18 ◇ (q16 ◇ q30)))))
  have apc20 : forall (q34 q8 q35 q36 q5 q6 q37 q38:G), (q8 ◇ q35) = (q34 ◇ q8):=by
    intro q34 q8 q35 q36 q5 q6 q37 q38
    exact (((((((((((cg (fun t => q8 ◇ t) (cg (fun t => q36 ◇ t) (cg (fun t => q5 ◇ t) (apc19 q6 q35 (q35 ◇ q6) (q35 ◇ q6) (q35 ◇ q6) (q35 ◇ q6) (q35 ◇ q6))))).trans (cg (fun t => q8 ◇ t) (cg (fun t => q36 ◇ t) (apc19 (q6 ◇ q35) q5 (q5 ◇ (q6 ◇ q35)) (q5 ◇ (q6 ◇ q35)) (q5 ◇ (q6 ◇ q35)) (q5 ◇ (q6 ◇ q35)) (q5 ◇ (q6 ◇ q35)))))).trans (cg (fun t => q8 ◇ t) (cg (fun t => q36 ◇ t) (apc17 q6 q35 q5)))).trans (cg (fun t => q8 ◇ t) (cg (fun t => q36 ◇ t) (apc19 q5 q35 (q35 ◇ q5) (q35 ◇ q5) (q35 ◇ q5) (q35 ◇ q5) (q35 ◇ q5))))).trans (cg (fun t => q8 ◇ t) (apc19 (q5 ◇ q35) q36 (q36 ◇ (q5 ◇ q35)) (q36 ◇ (q5 ◇ q35)) (q36 ◇ (q5 ◇ q35)) (q36 ◇ (q5 ◇ q35)) (q36 ◇ (q5 ◇ q35))))).trans (cg (fun t => q8 ◇ t) (apc17 q5 q35 q36))).trans (cg (fun t => q8 ◇ t) (apc19 q36 q35 (q35 ◇ q36) (q35 ◇ q36) (q35 ◇ q36) (q35 ◇ q36) (q35 ◇ q36)))).trans (apc19 (q36 ◇ q35) q8 (q8 ◇ (q36 ◇ q35)) (q8 ◇ (q36 ◇ q35)) (q8 ◇ (q36 ◇ q35)) (q8 ◇ (q36 ◇ q35)) (q8 ◇ (q36 ◇ q35)))).trans (apc17 q36 q35 q8)).trans (apc19 q8 q35 (q35 ◇ q8) (q35 ◇ q8) (q35 ◇ q8) (q35 ◇ q8) (q35 ◇ q8))).symm).trans ((((cg (fun t => q8 ◇ t) ((h q36 (q5 ◇ (q35 ◇ q6)) q34 q37 q38).symm)).symm).trans (apc0 q5 q6 (((q34 ◇ q37) ◇ q38) ◇ q36) q8 q35)).trans ((((((cg (fun t => t ◇ q8) (cg (fun t => t ◇ q36) (cg (fun t => t ◇ q38) (apc19 q37 q34 (q34 ◇ q37) (q34 ◇ q37) (q34 ◇ q37) (q34 ◇ q37) (q34 ◇ q37))))).trans (cg (fun t => t ◇ q8) (cg (fun t => t ◇ q36) (apc17 q37 q34 q38)))).trans (cg (fun t => t ◇ q8) (cg (fun t => t ◇ q36) (apc19 q38 q34 (q34 ◇ q38) (q34 ◇ q38) (q34 ◇ q38) (q34 ◇ q38) (q34 ◇ q38))))).trans (cg (fun t => t ◇ q8) (apc17 q38 q34 q36))).trans (cg (fun t => t ◇ q8) (apc19 q36 q34 (q34 ◇ q36) (q34 ◇ q36) (q34 ◇ q36) (q34 ◇ q36) (q34 ◇ q36)))).trans (apc17 q36 q34 q8)))
  exact (apc20 y x (y ◇ z) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z))).trans (apc20 ((x ◇ y) ◇ z) y x (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)) (x ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45536_to_57846 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45536_to_57846
