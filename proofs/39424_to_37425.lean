-- Equation39424 → Equation37425
-- Recorded verdict: true
-- Premise: x = (((y * z) * (x * y)) * y) * x
-- Conclusion: x = ((y * (x * (z * x))) * y) * x
-- Original submission SHA-256: 60d695776a0986922c8e3b18091790a1cf37eca127f9d5d40cb6d8c6b2ed9373
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ z) ◇ (x ◇ y)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (x ◇ (z ◇ x))) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((((y ◇ z) ◇ (x ◇ y)) ◇ y) ◇ x) = ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (q0:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact ((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc2 : forall (q1 q2:G), (((q2 ◇ (q1 ◇ (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2))) ◇ (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2)) ◇ q1) = q1:=by
    intro q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2)) (cg (fun t => t ◇ (q1 ◇ (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2))) (apc1 q2)))).symm).trans ((h q1 (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q2) q2).symm)
  have apc3 : forall (q3:G), (q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) = ((q3 ◇ q3) ◇ (q3 ◇ q3)):=by
    intro q3
    exact ((cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (apc2 q3 q3)).symm).trans ((h ((q3 ◇ q3) ◇ (q3 ◇ q3)) q3 (q3 ◇ (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ q3))).symm)
  have apc4 : forall (q4 q5:G), (((((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ (q4 ◇ q5)) ◇ q5) ◇ q4) = q4:=by
    intro q4 q5
    exact ((cg (fun t => t ◇ q4) (cg (fun t => t ◇ q5) (cg (fun t => t ◇ (q4 ◇ q5)) (apc3 q5)))).symm).trans ((h q4 q5 ((q5 ◇ q5) ◇ (q5 ◇ q5))).symm)
  have apc5 : forall (q6 q7 q8 q9:G), (((q9 ◇ (q8 ◇ (((q6 ◇ q7) ◇ (q9 ◇ q6)) ◇ q6))) ◇ (((q6 ◇ q7) ◇ (q9 ◇ q6)) ◇ q6)) ◇ q8) = q8:=by
    intro q6 q7 q8 q9
    exact ((cg (fun t => t ◇ q8) (cg (fun t => t ◇ (((q6 ◇ q7) ◇ (q9 ◇ q6)) ◇ q6)) (cg (fun t => t ◇ (q8 ◇ (((q6 ◇ q7) ◇ (q9 ◇ q6)) ◇ q6))) ((h q9 q6 q7).symm)))).symm).trans ((h q8 (((q6 ◇ q7) ◇ (q9 ◇ q6)) ◇ q6) q9).symm)
  have apc6 : forall (q10:G), (((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ q10) = q10:=by
    intro q10
    exact ((cg (fun t => t ◇ q10) (apc1 ((q10 ◇ q10) ◇ (q10 ◇ q10)))).symm).trans (((cg (fun t => t ◇ q10) (cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (cg (fun t => ((((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) ◇ (((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10)))) ◇ t) (apc3 q10)))).symm).trans (apc4 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10))))
  have apc7 : forall (q0:G), (q0 ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ q0) (apc6 q0)).symm).trans (apc1 q0)
  have apc8 : forall (q11 q12:G), (((q12 ◇ (q11 ◇ q12)) ◇ q12) ◇ q11) = q11:=by
    intro q11 q12
    exact (((((cg (fun t => t ◇ q11) (cg (fun t => (q12 ◇ (q11 ◇ q12)) ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => t ◇ (q12 ◇ q12)) (apc7 q12))))).trans (cg (fun t => t ◇ q11) (cg (fun t => (q12 ◇ (q11 ◇ q12)) ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => q12 ◇ t) (apc7 q12)))))).trans (cg (fun t => t ◇ q11) (cg (fun t => (q12 ◇ (q11 ◇ q12)) ◇ t) (cg (fun t => t ◇ q12) (apc7 q12))))).trans (cg (fun t => t ◇ q11) (cg (fun t => (q12 ◇ (q11 ◇ q12)) ◇ t) (apc7 q12)))).symm).trans (((cg (fun t => t ◇ q11) (cg (fun t => t ◇ (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ q12)) (cg (fun t => q12 ◇ t) (cg (fun t => q11 ◇ t) (apc6 q12))))).symm).trans (apc5 q12 q12 q11 q12))
  have apc9 : forall (q13 q14:G), (q14 ◇ ((q14 ◇ q13) ◇ q14)) = ((q14 ◇ q13) ◇ q14):=by
    intro q13 q14
    exact ((cg (fun t => q14 ◇ t) (cg (fun t => (q14 ◇ q13) ◇ t) (apc7 q14))).symm).trans ((((cg (fun t => t ◇ ((q14 ◇ q13) ◇ (q14 ◇ q14))) (apc5 q14 q13 q14 q14)).symm).trans ((h ((q14 ◇ q13) ◇ (q14 ◇ q14)) q14 (q14 ◇ (((q14 ◇ q13) ◇ (q14 ◇ q14)) ◇ q14))).symm)).trans (cg (fun t => (q14 ◇ q13) ◇ t) (apc7 q14)))
  have apc11 : forall (q15 q16:G), (((q16 ◇ q15) ◇ q16) ◇ q16) = q16:=by
    intro q15 q16
    exact (((cg (fun t => t ◇ q16) (cg (fun t => t ◇ ((q16 ◇ q15) ◇ q16)) (apc7 ((q16 ◇ q15) ◇ q16)))).trans (cg (fun t => t ◇ q16) (apc7 ((q16 ◇ q15) ◇ q16)))).symm).trans (((cg (fun t => t ◇ q16) (cg (fun t => t ◇ ((q16 ◇ q15) ◇ q16)) (cg (fun t => ((q16 ◇ q15) ◇ q16) ◇ t) (apc9 q15 q16)))).symm).trans (apc8 q16 ((q16 ◇ q15) ◇ q16)))
  have apc12 : forall (q15 q17:G), (q17 ◇ (q17 ◇ q15)) = (q17 ◇ q15):=by
    intro q15 q17
    exact ((cg (fun t => t ◇ (q17 ◇ q15)) (apc11 q15 q17)).symm).trans (((cg (fun t => t ◇ (q17 ◇ q15)) (cg (fun t => t ◇ q17) (apc9 q15 q17))).symm).trans (apc8 (q17 ◇ q15) q17))
  have apc13 : forall (q18 q19:G), ((q19 ◇ q18) ◇ q19) = q19:=by
    intro q18 q19
    exact (((cg (fun t => t ◇ q19) (cg (fun t => t ◇ (q19 ◇ q18)) (apc7 (q19 ◇ q18)))).trans (cg (fun t => t ◇ q19) (apc7 (q19 ◇ q18)))).symm).trans (((cg (fun t => t ◇ q19) (cg (fun t => t ◇ (q19 ◇ q18)) (cg (fun t => (q19 ◇ q18) ◇ t) (apc12 q18 q19)))).symm).trans (apc8 q19 (q19 ◇ q18)))
  have apc14 : forall (q11 q12:G), (q12 ◇ q11) = q11:=by
    intro q11 q12
    exact ((cg (fun t => t ◇ q11) (apc13 (q11 ◇ q12) q12)).symm).trans (apc8 q11 q12)
  exact (apc14 x ((y ◇ (x ◇ (z ◇ x))) ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_39424_to_37425 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_39424_to_37425
