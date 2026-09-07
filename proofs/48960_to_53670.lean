-- Equation48960 → Equation53670
-- Recorded verdict: true
-- Premise: x * y = ((y * y) * z) * (y * x)
-- Conclusion: x * y = (((z * w) * x) * x) * u
-- Original submission SHA-256: 97fed4005a4e92fb1a8f6d68d268cca5b17022f04ea3d661858aa9911c54c84e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ y) ◇ z) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (((z ◇ w) ◇ x) ◇ x) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q2)) = (q2 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q2)) ((h q0 q1 (q1 ◇ q1)).symm)).symm).trans ((h q2 (q1 ◇ q1) (q1 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), ((q3 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q4)) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ (q5 ◇ q4)) (apc0 q5 q5 q3)).symm).trans ((h q4 q5 ((q5 ◇ q5) ◇ q3)).symm)
  have apc2 : forall (q6 q7:G), ((q7 ◇ q7) ◇ (q7 ◇ q6)) = (q6 ◇ q7):=by
    intro q6 q7
    exact ((cg (fun t => t ◇ (q7 ◇ q6)) ((h q7 q7 q6).symm)).symm).trans (apc1 ((q7 ◇ q7) ◇ q6) q6 q7)
  have apc3 : forall (q8 q9 q10:G), ((q8 ◇ q10) ◇ (q10 ◇ q9)) = (q9 ◇ q10):=by
    intro q8 q9 q10
    exact ((cg (fun t => t ◇ (q10 ◇ q9)) (apc2 q8 q10)).symm).trans ((h q9 q10 (q10 ◇ q8)).symm)
  have apc4 : forall (q11 q9 q12:G), (((q11 ◇ q11) ◇ q12) ◇ ((q11 ◇ q11) ◇ q9)) = (q9 ◇ (q11 ◇ q11)):=by
    intro q11 q9 q12
    exact ((cg (fun t => t ◇ ((q11 ◇ q11) ◇ q9)) (cg (fun t => t ◇ q12) (apc2 q11 q11))).symm).trans ((h q9 (q11 ◇ q11) q12).symm)
  have apc5 : forall (x y z:G), (((y ◇ y) ◇ z) ◇ (y ◇ x)) = (((y ◇ y) ◇ x) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc6 : forall (q13 q14:G), (((q14 ◇ q14) ◇ q13) ◇ (q14 ◇ q13)) = (q13 ◇ q14):=by
    intro q13 q14
    exact ((apc5 q13 q14 q13).symm).trans ((h q13 q14 q13).symm)
  have apc7 : forall (q15:G), (q15 ◇ (q15 ◇ q15)) = (q15 ◇ q15):=by
    intro q15
    exact (((cg (fun t => ((q15 ◇ q15) ◇ q15) ◇ t) (apc3 q15 (q15 ◇ q15) q15)).trans (apc0 (q15 ◇ q15) q15 q15)).symm).trans ((((cg (fun t => t ◇ ((q15 ◇ q15) ◇ (q15 ◇ (q15 ◇ q15)))) (apc6 (q15 ◇ q15) q15)).symm).trans (apc6 (q15 ◇ (q15 ◇ q15)) (q15 ◇ q15))).trans (apc1 q15 q15 q15))
  have apc9 : forall (q16 q17:G), (((q16 ◇ q16) ◇ q17) ◇ (q16 ◇ q16)) = (q16 ◇ q16):=by
    intro q16 q17
    exact ((cg (fun t => ((q16 ◇ q16) ◇ q17) ◇ t) (apc3 q16 q16 q16)).symm).trans ((((cg (fun t => ((q16 ◇ q16) ◇ q17) ◇ t) (apc7 (q16 ◇ q16))).symm).trans (apc4 q16 ((q16 ◇ q16) ◇ (q16 ◇ q16)) q17)).trans ((cg (fun t => t ◇ (q16 ◇ q16)) (apc3 q16 q16 q16)).trans (apc3 q16 q16 q16)))
  have apc10 : forall (q18 q19:G), (q19 ◇ (q18 ◇ q18)) = ((q18 ◇ q18) ◇ q19):=by
    intro q18 q19
    exact (((apc3 (q18 ◇ q18) (q18 ◇ q18) q19).symm).trans ((((cg (fun t => ((q18 ◇ q18) ◇ q19) ◇ t) (apc4 q18 q19 q19)).symm).trans (apc7 ((q18 ◇ q18) ◇ q19))).trans (apc4 q18 q19 q19))).symm
  have apc11 : forall (q0 q1 q20 q21:G), (((((q1 ◇ q1) ◇ q20) ◇ ((q1 ◇ q1) ◇ q20)) ◇ q21) ◇ (q0 ◇ q1)) = ((q1 ◇ q0) ◇ ((q1 ◇ q1) ◇ q20)):=by
    intro q0 q1 q20 q21
    exact ((cg (fun t => ((((q1 ◇ q1) ◇ q20) ◇ ((q1 ◇ q1) ◇ q20)) ◇ q21) ◇ t) ((h q0 q1 q20).symm)).symm).trans ((h (q1 ◇ q0) ((q1 ◇ q1) ◇ q20) q21).symm)
  have apc12 : forall (q22 q23 q24:G), ((q22 ◇ q22) ◇ q23) = (q22 ◇ q22):=by
    intro q22 q23 q24
    exact (((((cg (fun t => t ◇ (q23 ◇ (q22 ◇ q22))) (cg (fun t => (q22 ◇ q24) ◇ t) (apc3 q22 q22 q22))).trans (cg (fun t => ((q22 ◇ q24) ◇ (q22 ◇ q22)) ◇ t) (apc10 q22 q23))).trans (apc3 (q22 ◇ q24) q23 (q22 ◇ q22))).trans (apc10 q22 q23)).symm).trans ((((cg (fun t => t ◇ (q23 ◇ (q22 ◇ q22))) (apc11 q24 q22 (q22 ◇ q22) (((q22 ◇ q22) ◇ (q22 ◇ q22)) ◇ ((q22 ◇ q22) ◇ (q22 ◇ q22))))).symm).trans (apc11 q23 (q22 ◇ q22) ((q22 ◇ q22) ◇ (q22 ◇ q22)) (q24 ◇ q22))).trans ((((cg (fun t => ((q22 ◇ q22) ◇ q23) ◇ t) (cg (fun t => t ◇ ((q22 ◇ q22) ◇ (q22 ◇ q22))) (apc3 q22 q22 q22))).trans (cg (fun t => ((q22 ◇ q22) ◇ q23) ◇ t) (cg (fun t => (q22 ◇ q22) ◇ t) (apc3 q22 q22 q22)))).trans (cg (fun t => ((q22 ◇ q22) ◇ q23) ◇ t) (apc3 q22 q22 q22))).trans (apc9 q22 q23)))
  have apc13 : forall (q24 q22 q23 q13 q14:G), (q14 ◇ q14) = (q13 ◇ q14):=by
    intro q24 q22 q23 q13 q14
    exact (((cg (fun t => t ◇ (q14 ◇ q13)) (apc12 q14 q13 ((q14 ◇ q14) ◇ q13))).trans (apc12 q14 (q14 ◇ q13) ((q14 ◇ q14) ◇ (q14 ◇ q13)))).symm).trans (apc6 q13 q14)
  have apc14 : forall (q25 q26 q27:G), ((q25 ◇ q26) ◇ q27) = (q26 ◇ q26):=by
    intro q25 q26 q27
    exact ((cg (fun t => t ◇ q27) (apc13 q25 q25 q25 q25 q26)).symm).trans (apc12 q26 q27 q25)
  have apc16 : forall (q28 q29 q30:G), (q29 ◇ q30) = (q28 ◇ q28):=by
    intro q28 q29 q30
    exact (((apc14 q28 q28 (q30 ◇ q29)).symm).trans (((cg (fun t => t ◇ (q30 ◇ q29)) (apc12 q28 q30 q28)).symm).trans (apc3 (q28 ◇ q28) q29 q30))).symm
  exact (apc16 (x ◇ y) x y).trans ((apc16 (x ◇ y) (((z ◇ w) ◇ x) ◇ x) u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48960_to_53670 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48960_to_53670
