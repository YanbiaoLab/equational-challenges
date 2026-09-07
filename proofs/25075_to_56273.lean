-- Equation25075 → Equation56273
-- Recorded verdict: true
-- Premise: x = (y * (x * (x * x))) * (z * x)
-- Conclusion: x * (y * z) = (z * w) * (x * z)
-- Original submission SHA-256: c6e2f54b32083a4466439b5d032c27cf7e3be7f0e63946ccd58d8866b2d95181
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (x ◇ x))) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (z ◇ w) ◇ (x ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q0)) ((h (q0 ◇ q0) q0 q0).symm)).symm).trans ((h q0 (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) q1).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ (q3 ◇ (q2 ◇ q2))) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ (q2 ◇ q2))) (apc0 q2 q2)).symm).trans (apc0 (q2 ◇ q2) q3)
  have apc5 : forall (q2 q4:G), (((q4 ◇ q2) ◇ (q4 ◇ q2)) ◇ q2) = (q4 ◇ q2):=by
    intro q2 q4
    exact ((cg (fun t => ((q4 ◇ q2) ◇ (q4 ◇ q2)) ◇ t) (apc0 q2 q4)).symm).trans (apc0 (q4 ◇ q2) (q2 ◇ q2))
  have apc7 : forall (q5:G), (q5 ◇ (q5 ◇ q5)) = q5:=by
    intro q5
    exact ((apc5 (q5 ◇ q5) q5).symm).trans ((h q5 (q5 ◇ (q5 ◇ q5)) q5).symm)
  have apc8 : forall (q6 q7 q8:G), ((q8 ◇ (q7 ◇ q6)) ◇ q6) = (q7 ◇ q6):=by
    intro q6 q7 q8
    exact ((cg (fun t => t ◇ q6) (cg (fun t => q8 ◇ t) (apc7 (q7 ◇ q6)))).symm).trans (((cg (fun t => (q8 ◇ ((q7 ◇ q6) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6)))) ◇ t) ((h q6 q6 q7).symm)).symm).trans ((h (q7 ◇ q6) q8 (q6 ◇ (q6 ◇ (q6 ◇ q6)))).symm))
  have apc9 : forall (q9 q10 q11 q12:G), ((q12 ◇ q9) ◇ (q11 ◇ q9)) = ((q10 ◇ q9) ◇ (q11 ◇ q9)):=by
    intro q9 q10 q11 q12
    exact (((cg (fun t => t ◇ (q11 ◇ q9)) (cg (fun t => q12 ◇ t) ((h q9 q10 q11).symm))).symm).trans (apc8 (q11 ◇ q9) (q10 ◇ (q9 ◇ (q9 ◇ q9))) q12)).trans (cg (fun t => t ◇ (q11 ◇ q9)) (cg (fun t => q10 ◇ t) (apc7 q9)))
  have apc10 : forall (q9 q10 q11 q12:G), ((q10 ◇ q9) ◇ (q11 ◇ q9)) = q9:=by
    intro q9 q10 q11 q12
    exact (((apc9 q9 q10 q11 q12).symm).trans (apc9 q9 q9 q11 q12)).trans (apc0 q9 q11)
  have apc12 : forall (q13 q14:G), (q13 ◇ (q14 ◇ q14)) = q14:=by
    intro q13 q14
    exact (((apc10 q14 q14 q14 ((q14 ◇ q14) ◇ (q14 ◇ q14))).symm).trans (((cg (fun t => t ◇ (q14 ◇ q14)) (apc1 q14 q13)).symm).trans (apc8 (q14 ◇ q14) q13 q14))).symm
  have apc14 : forall (q15 q16:G), (q16 ◇ q15) = (q15 ◇ q15):=by
    intro q15 q16
    exact (((cg (fun t => t ◇ q15) (apc0 q15 q16)).symm).trans (apc8 q15 q16 (q15 ◇ q15))).symm
  have apc15 : forall (q17 q18 q19 q20:G), ((q18 ◇ q19) ◇ (q18 ◇ q19)) = ((q17 ◇ q19) ◇ (q18 ◇ q19)):=by
    intro q17 q18 q19 q20
    exact (((cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => q18 ◇ t) (apc12 q20 q19))).trans (apc14 (q18 ◇ q19) (q19 ◇ q19))).symm).trans ((((cg (fun t => t ◇ (q18 ◇ (q20 ◇ (q19 ◇ q19)))) (apc1 q19 q20)).symm).trans (apc9 (q20 ◇ (q19 ◇ q19)) q17 q18 q19)).trans ((cg (fun t => t ◇ (q18 ◇ (q20 ◇ (q19 ◇ q19)))) (cg (fun t => q17 ◇ t) (apc12 q20 q19))).trans (cg (fun t => (q17 ◇ q19) ◇ t) (cg (fun t => q18 ◇ t) (apc12 q20 q19)))))
  have apc16 : forall (q21 q22 q23:G), ((q21 ◇ q22) ◇ (q21 ◇ q22)) = q22:=by
    intro q21 q22 q23
    exact (((apc12 (q23 ◇ q22) q22).symm).trans (((cg (fun t => (q23 ◇ q22) ◇ t) (apc14 q22 q21)).symm).trans ((apc15 q23 q21 q22 q23).symm))).symm
  have apc17 : forall (q24 q25 q26 q27:G), (q25 ◇ (q26 ◇ (q24 ◇ q25))) = (q24 ◇ q25):=by
    intro q24 q25 q26 q27
    exact (((cg (fun t => t ◇ (q26 ◇ (q24 ◇ q25))) (cg (fun t => q27 ◇ t) (apc14 q25 (q24 ◇ q25)))).trans (cg (fun t => t ◇ (q26 ◇ (q24 ◇ q25))) (apc12 q27 q25))).symm).trans (((cg (fun t => t ◇ (q26 ◇ (q24 ◇ q25))) (cg (fun t => q27 ◇ t) (cg (fun t => (q24 ◇ q25) ◇ t) (apc16 q24 q25 q24)))).symm).trans ((h (q24 ◇ q25) q27 q26).symm))
  have apc18 : forall (q28 q29 q30:G), (q29 ◇ (q28 ◇ q30)) = q30:=by
    intro q28 q29 q30
    exact ((((cg (fun t => (q28 ◇ q30) ◇ t) (apc17 q28 q30 q29 (q30 ◇ (q29 ◇ (q28 ◇ q30))))).trans (apc16 q28 q30 ((q28 ◇ q30) ◇ (q28 ◇ q30)))).symm).trans (((cg (fun t => t ◇ (q30 ◇ (q29 ◇ (q28 ◇ q30)))) (apc17 q28 q30 q29 q28)).symm).trans (apc16 q30 (q29 ◇ (q28 ◇ q30)) q28))).symm
  exact (apc18 y x z).trans ((apc18 x (z ◇ w) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25075_to_56273 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25075_to_56273
