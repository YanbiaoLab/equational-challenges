-- Equation21732 → Equation61893
-- Recorded verdict: true
-- Premise: x = (y * (y * x)) * (z * (x * x))
-- Conclusion: (x * x) * y = ((z * w) * w) * y
-- Original submission SHA-256: 8229d91e6bad3ce95f7daf0d90af0b9dc3744e51657c1ea438d98f253285ca40
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ x)) ◇ (z ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = ((z ◇ w) ◇ w) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ (q0 ◇ q0))) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q0))) ◇ t) ((h q0 q0 (q0 ◇ q0)).symm)).symm).trans ((h (q0 ◇ q0) q1 (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q2 q3:G), (((q3 ◇ (q3 ◇ q2)) ◇ q2) ◇ (q2 ◇ q2)) = ((q2 ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q2 q3
    exact ((cg (fun t => t ◇ (q2 ◇ q2)) (cg (fun t => (q3 ◇ (q3 ◇ q2)) ◇ t) ((h q2 q3 (q2 ◇ q2)).symm))).symm).trans (apc0 (q2 ◇ q2) (q3 ◇ (q3 ◇ q2)))
  have apc2 : forall (q4 q5:G), ((q5 ◇ (q5 ◇ q4)) ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) = q4:=by
    intro q4 q5
    exact ((cg (fun t => (q5 ◇ (q5 ◇ q4)) ◇ t) (apc0 (q4 ◇ q4) q4)).symm).trans ((h q4 q5 (q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))))).symm)
  have apc3 : forall (x y z:G), ((y ◇ (y ◇ x)) ◇ (z ◇ (x ◇ x))) = ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc5 : forall (x y z q4 q5:G), ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ (q4 ◇ q4))) = q4:=by
    intro x y z q4 q5
    exact ((apc3 q4 q5 (q4 ◇ q4)).symm).trans (apc2 q4 q5)
  have apc6 : forall (q6 q7:G), (((q6 ◇ (q6 ◇ q6)) ◇ q6) ◇ (q7 ◇ q6)) = (q6 ◇ (q6 ◇ q6)):=by
    intro q6 q7
    exact ((cg (fun t => ((q6 ◇ (q6 ◇ q6)) ◇ q6) ◇ t) (cg (fun t => q7 ◇ t) (apc5 ((q6 ◇ (q6 ◇ q6)) ◇ (q6 ◇ (q6 ◇ q6))) ((q6 ◇ (q6 ◇ q6)) ◇ (q6 ◇ (q6 ◇ q6))) ((q6 ◇ (q6 ◇ q6)) ◇ (q6 ◇ (q6 ◇ q6))) q6 ((q6 ◇ (q6 ◇ q6)) ◇ (q6 ◇ (q6 ◇ q6)))))).symm).trans (((cg (fun t => t ◇ (q7 ◇ ((q6 ◇ (q6 ◇ q6)) ◇ (q6 ◇ (q6 ◇ q6))))) (cg (fun t => (q6 ◇ (q6 ◇ q6)) ◇ t) (apc5 q6 q6 q6 q6 q6))).symm).trans ((h (q6 ◇ (q6 ◇ q6)) (q6 ◇ (q6 ◇ q6)) q7).symm))
  have apc7 : forall (q8:G), ((q8 ◇ q8) ◇ (q8 ◇ q8)) = (q8 ◇ (q8 ◇ q8)):=by
    intro q8
    exact ((apc1 q8 q8).symm).trans (((cg (fun t => ((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ t) (apc0 q8 q8)).symm).trans (apc6 q8 (q8 ◇ (q8 ◇ (q8 ◇ q8)))))
  have apc8 : forall (q9:G), ((q9 ◇ (q9 ◇ q9)) ◇ q9) = (q9 ◇ q9):=by
    intro q9
    exact (((cg (fun t => q9 ◇ t) (apc5 ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) q9 ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))))).symm).trans ((((cg (fun t => t ◇ ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9)))) ((h q9 q9 q9).symm)).symm).trans (apc7 (q9 ◇ (q9 ◇ q9)))).trans (cg (fun t => (q9 ◇ (q9 ◇ q9)) ◇ t) (apc5 ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))) q9 ((q9 ◇ (q9 ◇ q9)) ◇ (q9 ◇ (q9 ◇ q9))))))).symm
  have apc9 : forall (q0 q10:G), (q0 ◇ (q10 ◇ (q0 ◇ (q0 ◇ q0)))) = (q0 ◇ q0):=by
    intro q0 q10
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q10 ◇ t) (apc7 q0))).symm).trans (((cg (fun t => t ◇ (q10 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) ((h q0 q0 (q0 ◇ (q0 ◇ q0))).symm)).symm).trans ((h (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)) q10).symm))
  have apc11 : forall (q11:G), ((q11 ◇ q11) ◇ (q11 ◇ (q11 ◇ q11))) = q11:=by
    intro q11
    exact ((((cg (fun t => (q11 ◇ (q11 ◇ q11)) ◇ t) (apc7 q11)).trans (apc5 ((q11 ◇ (q11 ◇ q11)) ◇ (q11 ◇ (q11 ◇ q11))) ((q11 ◇ (q11 ◇ q11)) ◇ (q11 ◇ (q11 ◇ q11))) ((q11 ◇ (q11 ◇ q11)) ◇ (q11 ◇ (q11 ◇ q11))) q11 ((q11 ◇ (q11 ◇ q11)) ◇ (q11 ◇ (q11 ◇ q11))))).symm).trans ((((cg (fun t => t ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (apc7 q11)).symm).trans (apc7 (q11 ◇ q11))).trans (cg (fun t => (q11 ◇ q11) ◇ t) (apc7 q11)))).symm
  have apc15 : forall (q0 q12 q13 q10:G), (((q12 ◇ (q12 ◇ q0)) ◇ q0) ◇ (q10 ◇ ((q13 ◇ (q0 ◇ q0)) ◇ (q13 ◇ (q0 ◇ q0))))) = (q13 ◇ (q0 ◇ q0)):=by
    intro q0 q12 q13 q10
    exact ((cg (fun t => t ◇ (q10 ◇ ((q13 ◇ (q0 ◇ q0)) ◇ (q13 ◇ (q0 ◇ q0))))) (cg (fun t => (q12 ◇ (q12 ◇ q0)) ◇ t) ((h q0 q12 q13).symm))).symm).trans ((h (q13 ◇ (q0 ◇ q0)) (q12 ◇ (q12 ◇ q0)) q10).symm)
  have apc17 : forall (q9 q6 q7:G), ((q6 ◇ q6) ◇ (q7 ◇ q6)) = (q6 ◇ (q6 ◇ q6)):=by
    intro q9 q6 q7
    exact ((cg (fun t => t ◇ (q7 ◇ q6)) (apc8 q6)).symm).trans (apc6 q6 q7)
  have apc20 : forall (q14 q15 q16:G), (((q15 ◇ (q15 ◇ q14)) ◇ q14) ◇ (q16 ◇ q14)) = (q14 ◇ (q14 ◇ q14)):=by
    intro q14 q15 q16
    exact (((((cg (fun t => ((q15 ◇ (q15 ◇ q14)) ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => ((q14 ◇ q14) ◇ (q14 ◇ q14)) ◇ t) (cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => (q14 ◇ q14) ◇ t) (apc17 ((q14 ◇ q14) ◇ (q14 ◇ q14)) q14 q14)))))).trans (cg (fun t => ((q15 ◇ (q15 ◇ q14)) ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => ((q14 ◇ q14) ◇ (q14 ◇ q14)) ◇ t) (cg (fun t => t ◇ (q14 ◇ q14)) (apc11 q14)))))).trans (cg (fun t => ((q15 ◇ (q15 ◇ q14)) ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ (q14 ◇ (q14 ◇ q14))) (apc17 ((q14 ◇ q14) ◇ (q14 ◇ q14)) q14 q14))))).trans (cg (fun t => ((q15 ◇ (q15 ◇ q14)) ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (apc5 ((q14 ◇ (q14 ◇ q14)) ◇ (q14 ◇ (q14 ◇ q14))) ((q14 ◇ (q14 ◇ q14)) ◇ (q14 ◇ (q14 ◇ q14))) ((q14 ◇ (q14 ◇ q14)) ◇ (q14 ◇ (q14 ◇ q14))) q14 ((q14 ◇ (q14 ◇ q14)) ◇ (q14 ◇ (q14 ◇ q14))))))).symm).trans ((((cg (fun t => ((q15 ◇ (q15 ◇ q14)) ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ (((q14 ◇ q14) ◇ ((q14 ◇ q14) ◇ (q14 ◇ q14))) ◇ (q14 ◇ q14))) (apc8 (q14 ◇ q14))))).symm).trans (apc15 q14 q15 ((q14 ◇ q14) ◇ ((q14 ◇ q14) ◇ (q14 ◇ q14))) q16)).trans ((cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => (q14 ◇ q14) ◇ t) (apc17 ((q14 ◇ q14) ◇ (q14 ◇ q14)) q14 q14))).trans (cg (fun t => t ◇ (q14 ◇ q14)) (apc11 q14))))
  have apc21 : forall (q17 q18:G), ((q18 ◇ (q18 ◇ q17)) ◇ (q17 ◇ (q17 ◇ q17))) = q17:=by
    intro q17 q18
    exact (((cg (fun t => t ◇ (q17 ◇ (q17 ◇ q17))) (cg (fun t => q18 ◇ t) (cg (fun t => q18 ◇ t) (apc5 q17 q17 q17 q17 q17)))).symm).trans (apc0 (q17 ◇ (q17 ◇ q17)) q18)).trans (apc5 ((q17 ◇ (q17 ◇ q17)) ◇ (q17 ◇ (q17 ◇ q17))) ((q17 ◇ (q17 ◇ q17)) ◇ (q17 ◇ (q17 ◇ q17))) ((q17 ◇ (q17 ◇ q17)) ◇ (q17 ◇ (q17 ◇ q17))) q17 ((q17 ◇ (q17 ◇ q17)) ◇ (q17 ◇ (q17 ◇ q17))))
  have apc30 : forall (q19 q20 q21:G), (q19 ◇ (q21 ◇ ((q20 ◇ q19) ◇ (q20 ◇ q19)))) = (q20 ◇ q19):=by
    intro q19 q20 q21
    exact ((cg (fun t => t ◇ (q21 ◇ ((q20 ◇ q19) ◇ (q20 ◇ q19)))) (apc11 q19)).symm).trans (((cg (fun t => t ◇ (q21 ◇ ((q20 ◇ q19) ◇ (q20 ◇ q19)))) (cg (fun t => (q19 ◇ q19) ◇ t) (apc17 q19 q19 q20))).symm).trans ((h (q20 ◇ q19) (q19 ◇ q19) q21).symm))
  have apc31 : forall (q22 q23 q24:G), ((q22 ◇ (q22 ◇ q23)) ◇ q23) = (q23 ◇ q23):=by
    intro q22 q23 q24
    exact (((apc9 q23 q24).symm).trans (((cg (fun t => q23 ◇ t) (cg (fun t => q24 ◇ t) (apc20 q23 q22 (q22 ◇ (q22 ◇ q23))))).symm).trans (apc30 q23 (q22 ◇ (q22 ◇ q23)) q24))).symm
  have apc33 : forall (q25 q26 q27:G), ((q26 ◇ q25) ◇ (q27 ◇ q25)) = (q25 ◇ (q25 ◇ q25)):=by
    intro q25 q26 q27
    exact (((cg (fun t => (q26 ◇ q25) ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => (q25 ◇ (q25 ◇ q25)) ◇ t) (apc17 ((q25 ◇ q25) ◇ (q26 ◇ q25)) q25 q26)))).trans (cg (fun t => (q26 ◇ q25) ◇ t) (cg (fun t => q27 ◇ t) (apc21 q25 q25)))).symm).trans ((((cg (fun t => (q26 ◇ q25) ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => t ◇ ((q25 ◇ q25) ◇ (q26 ◇ q25))) (apc17 q25 q25 q26)))).symm).trans (apc30 (q26 ◇ q25) (q25 ◇ q25) q27)).trans (apc17 ((q25 ◇ q25) ◇ (q26 ◇ q25)) q25 q26))
  have apc34 : forall (q28 q29 q30:G), (q29 ◇ q28) = (q28 ◇ q28):=by
    intro q28 q29 q30
    exact ((((((cg (fun t => ((q30 ◇ q28) ◇ (q28 ◇ (q28 ◇ q28))) ◇ t) (cg (fun t => (q29 ◇ q28) ◇ t) (apc33 q28 q29 q29))).trans (apc33 (q28 ◇ (q28 ◇ q28)) (q30 ◇ q28) (q29 ◇ q28))).trans (cg (fun t => (q28 ◇ (q28 ◇ q28)) ◇ t) (apc21 q28 q28))).trans (apc31 q28 q28 ((q28 ◇ (q28 ◇ q28)) ◇ q28))).symm).trans (((cg (fun t => t ◇ ((q29 ◇ q28) ◇ ((q29 ◇ q28) ◇ (q29 ◇ q28)))) (cg (fun t => (q30 ◇ q28) ◇ t) (apc33 q28 q30 q29))).symm).trans (apc21 (q29 ◇ q28) (q30 ◇ q28)))).symm
  exact (apc34 y (x ◇ x) ((x ◇ x) ◇ y)).trans ((apc34 y ((z ◇ w) ◇ w) ((x ◇ x) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21732_to_61893 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21732_to_61893
