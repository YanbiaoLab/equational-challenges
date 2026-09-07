-- Equation29507 → Equation29470
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ (y ◇ (y ◇ z)))) ◇ x
-- Conclusion: x = (y ◇ (x ◇ (x ◇ (y ◇ z)))) ◇ x
-- Original submission SHA-256: 1f1bb70f2eb9761f68c30d80df12cc1dbac4d0c1a3ad4f508be615db8ddd1a71
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (y ◇ (y ◇ z)))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (x ◇ (y ◇ z)))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (x ◇ (y ◇ (y ◇ z)))) ◇ x) = ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1:G), (((q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) ◇ (q0 ◇ q1)) ◇ q0) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) ◇ t) (cg (fun t => q0 ◇ t) (apc1 q1 ((q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) ◇ q1) ((q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) ◇ q1))))).symm).trans (((cg (fun t => t ◇ q0) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) ◇ t) (apc1 q1 q0 q0))))).symm).trans ((h q0 (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) q1).symm))
  have apc3 : forall (q2 q3 q4:G), (q4 ◇ (q2 ◇ (q4 ◇ (q2 ◇ (q2 ◇ q3))))) = (q2 ◇ (q4 ◇ (q2 ◇ (q2 ◇ q3)))):=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ (q2 ◇ (q4 ◇ (q2 ◇ (q2 ◇ q3))))) (apc1 q4 ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4) ((q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ q4))).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q4 ◇ (q2 ◇ (q2 ◇ q3))))) (cg (fun t => (q4 ◇ (q4 ◇ (q4 ◇ (q4 ◇ q4)))) ◇ t) ((h q4 q2 q3).symm))).symm).trans (apc2 (q2 ◇ (q4 ◇ (q2 ◇ (q2 ◇ q3)))) q4))
  have apc4 : forall (q5 q6:G), ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q5)))) ◇ q6) = q6:=by
    intro q5 q6
    exact ((cg (fun t => t ◇ q6) (apc3 q6 q5 q6)).symm).trans ((h q6 q6 (q6 ◇ q5)).symm)
  have apc6 : forall (q7 q5 q8 q6:G), ((q6 ◇ (q8 ◇ (q7 ◇ (q6 ◇ (q7 ◇ (q7 ◇ q5)))))) ◇ q8) = q8:=by
    intro q7 q5 q8 q6
    exact ((cg (fun t => t ◇ q8) (cg (fun t => q6 ◇ t) (cg (fun t => q8 ◇ t) (apc3 q7 q5 q6)))).symm).trans (((cg (fun t => t ◇ q8) (cg (fun t => q6 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => q6 ◇ t) (apc3 q7 q5 q6))))).symm).trans ((h q8 q6 (q7 ◇ (q6 ◇ (q7 ◇ (q7 ◇ q5))))).symm))
  have apc7 : forall (q9 q10 q11:G), (((q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q9)))) ◇ (q10 ◇ q11)) ◇ q10) = q10:=by
    intro q9 q10 q11
    exact ((cg (fun t => t ◇ q10) (cg (fun t => (q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q9)))) ◇ t) (cg (fun t => q10 ◇ t) (apc4 q9 q11)))).symm).trans (((cg (fun t => t ◇ q10) (cg (fun t => (q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q9)))) ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => (q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q9)))) ◇ t) (apc4 q9 q11))))).symm).trans ((h q10 (q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q9)))) q11).symm))
  have apc8 : forall (q12 q13 q14 q15:G), (((q12 ◇ (q15 ◇ (q12 ◇ (q12 ◇ q13)))) ◇ (q14 ◇ q15)) ◇ q14) = q14:=by
    intro q12 q13 q14 q15
    exact ((((cg (fun t => t ◇ q14) (cg (fun t => t ◇ (q14 ◇ q15)) (cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (apc3 q12 q13 q15))))).trans (cg (fun t => t ◇ q14) (cg (fun t => t ◇ (q14 ◇ q15)) (cg (fun t => q15 ◇ t) (apc3 q12 q13 q15))))).trans (cg (fun t => t ◇ q14) (cg (fun t => t ◇ (q14 ◇ q15)) (apc3 q12 q13 q15)))).symm).trans (((cg (fun t => t ◇ q14) (cg (fun t => t ◇ (q14 ◇ q15)) (cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (apc3 q12 q13 q15)))))).symm).trans (apc7 (q12 ◇ (q15 ◇ (q12 ◇ (q12 ◇ q13)))) q14 q15))
  have apc10 : forall (q16 q17 q18 q19:G), (q19 ◇ (q18 ◇ (q19 ◇ (q16 ◇ (q18 ◇ (q16 ◇ (q16 ◇ q17))))))) = (q18 ◇ (q19 ◇ (q16 ◇ (q18 ◇ (q16 ◇ (q16 ◇ q17)))))):=by
    intro q16 q17 q18 q19
    exact ((cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => q19 ◇ t) (apc3 q16 q17 q18)))).symm).trans ((((cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (apc3 q16 q17 q18))))).symm).trans (apc3 q18 (q16 ◇ (q18 ◇ (q16 ◇ (q16 ◇ q17)))) q19)).trans ((cg (fun t => q18 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (apc3 q16 q17 q18)))).trans (cg (fun t => q18 ◇ t) (cg (fun t => q19 ◇ t) (apc3 q16 q17 q18)))))
  have apc11 : forall (q20 q21 q22:G), ((q21 ◇ (q22 ◇ (q22 ◇ (q21 ◇ (q22 ◇ (q22 ◇ q20)))))) ◇ q21) = q21:=by
    intro q20 q21 q22
    exact ((cg (fun t => t ◇ q21) (apc10 q22 q20 q21 q22)).symm).trans ((h q21 q22 (q21 ◇ (q22 ◇ (q22 ◇ q20)))).symm)
  have apc13 : forall (q23 q24 q25:G), ((((q23 ◇ (q23 ◇ (q23 ◇ (q23 ◇ q23)))) ◇ (q25 ◇ q23)) ◇ (q24 ◇ q25)) ◇ q24) = q24:=by
    intro q23 q24 q25
    exact ((cg (fun t => t ◇ q24) (cg (fun t => ((q23 ◇ (q23 ◇ (q23 ◇ (q23 ◇ q23)))) ◇ (q25 ◇ q23)) ◇ t) (cg (fun t => q24 ◇ t) (apc8 q23 q23 q25 q23)))).symm).trans (((cg (fun t => t ◇ q24) (cg (fun t => ((q23 ◇ (q23 ◇ (q23 ◇ (q23 ◇ q23)))) ◇ (q25 ◇ q23)) ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => ((q23 ◇ (q23 ◇ (q23 ◇ (q23 ◇ q23)))) ◇ (q25 ◇ q23)) ◇ t) (apc2 q25 q23))))).symm).trans ((h q24 ((q23 ◇ (q23 ◇ (q23 ◇ (q23 ◇ q23)))) ◇ (q25 ◇ q23)) q25).symm))
  have apc17 : forall (q26 q27 q28 q29 q30:G), (((q28 ◇ (q30 ◇ (q26 ◇ (q28 ◇ (q26 ◇ (q26 ◇ q27)))))) ◇ (q29 ◇ q30)) ◇ q29) = q29:=by
    intro q26 q27 q28 q29 q30
    exact ((cg (fun t => t ◇ q29) (cg (fun t => (q28 ◇ (q30 ◇ (q26 ◇ (q28 ◇ (q26 ◇ (q26 ◇ q27)))))) ◇ t) (cg (fun t => q29 ◇ t) (apc6 q26 q27 q30 q28)))).symm).trans (((cg (fun t => t ◇ q29) (cg (fun t => (q28 ◇ (q30 ◇ (q26 ◇ (q28 ◇ (q26 ◇ (q26 ◇ q27)))))) ◇ t) (cg (fun t => q29 ◇ t) (cg (fun t => (q28 ◇ (q30 ◇ (q26 ◇ (q28 ◇ (q26 ◇ (q26 ◇ q27)))))) ◇ t) (apc6 q26 q27 q30 q28))))).symm).trans ((h q29 (q28 ◇ (q30 ◇ (q26 ◇ (q28 ◇ (q26 ◇ (q26 ◇ q27)))))) q30).symm))
  have apc18 : forall (q31 q32:G), ((q32 ◇ q31) ◇ q32) = q32:=by
    intro q31 q32
    exact ((cg (fun t => t ◇ q32) (apc11 q31 (q32 ◇ q31) q31)).symm).trans (apc17 q31 q31 (q32 ◇ q31) q32 q31)
  have apc19 : forall (q33 q34:G), (q34 ◇ (q34 ◇ q33)) = (q34 ◇ q33):=by
    intro q33 q34
    exact ((cg (fun t => t ◇ (q34 ◇ q33)) (apc18 q33 q34)).symm).trans (apc18 q34 (q34 ◇ q33))
  have apc21 : forall (q35 q36 q37:G), ((q36 ◇ (q37 ◇ (q36 ◇ q35))) ◇ q37) = q37:=by
    intro q35 q36 q37
    exact (((((cg (fun t => t ◇ q37) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ q35))) (cg (fun t => t ◇ q36) (cg (fun t => q36 ◇ t) (cg (fun t => q36 ◇ t) (apc19 q36 q36)))))).trans (cg (fun t => t ◇ q37) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ q35))) (cg (fun t => t ◇ q36) (cg (fun t => q36 ◇ t) (apc19 q36 q36)))))).trans (cg (fun t => t ◇ q37) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ q35))) (cg (fun t => t ◇ q36) (apc19 q36 q36))))).trans (cg (fun t => t ◇ q37) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ q35))) (apc18 q36 q36)))).symm).trans (((cg (fun t => t ◇ q37) (cg (fun t => t ◇ (q37 ◇ (q36 ◇ q35))) (cg (fun t => (q36 ◇ (q36 ◇ (q36 ◇ (q36 ◇ q36)))) ◇ t) (apc18 q35 q36)))).symm).trans (apc13 q36 q37 (q36 ◇ q35)))
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (x ◇ (x ◇ (y ◇ z)))) ◇ x):=((cg (fun t => t ◇ x) (cg (fun t => y ◇ t) (apc19 (y ◇ z) x))).trans (apc21 z y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29507_to_29470 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29507_to_29470
