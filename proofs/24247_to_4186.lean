-- Equation24247 → Equation4186
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ y) ◇ ((y ◇ z) ◇ z)
-- Conclusion: x ◇ y = ((y ◇ z) ◇ w) ◇ x
-- Original submission SHA-256: 24bd935f48b0a3c2b776017a680a623e6d2df746383665a6c18fdd64fb8a7906
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ ((y ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ z) ◇ w) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ x) ◇ y) ◇ ((y ◇ z) ◇ z)) = (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (apc1 q0 (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))))).symm).trans (((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) ((h q0 q0 q0).symm))).symm).trans (apc1 ((q0 ◇ q0) ◇ q0) q0 q0))
  have apc3 : forall (q1 q2 q3 q4:G), ((q1 ◇ ((q2 ◇ q1) ◇ q2)) ◇ ((((q2 ◇ q1) ◇ q2) ◇ q4) ◇ q4)) = ((q2 ◇ q3) ◇ q3):=by
    intro q1 q2 q3 q4
    exact ((cg (fun t => t ◇ ((((q2 ◇ q1) ◇ q2) ◇ q4) ◇ q4)) (cg (fun t => t ◇ ((q2 ◇ q1) ◇ q2)) ((h q1 q2 q3).symm))).symm).trans ((h ((q2 ◇ q3) ◇ q3) ((q2 ◇ q1) ◇ q2) q4).symm)
  have apc4 : forall (q1 q2 q3 q4:G), ((q2 ◇ q3) ◇ q3) = ((q2 ◇ q1) ◇ q1):=by
    intro q1 q2 q3 q4
    exact ((apc3 q1 q2 q3 q1).symm).trans (apc3 q1 q2 q1 q1)
  have apc5 : forall (q5 q6:G), ((q5 ◇ q6) ◇ q6) = ((q5 ◇ q5) ◇ q5):=by
    intro q5 q6
    exact (((apc2 q5).symm).trans (((cg (fun t => (q5 ◇ ((q5 ◇ q5) ◇ q5)) ◇ t) (cg (fun t => t ◇ ((q5 ◇ q5) ◇ q5)) (apc1 q5 q5 q5))).symm).trans (apc3 q5 q5 q6 ((q5 ◇ q5) ◇ q5)))).symm
  have apc6 : forall (q7 q8 q9 q10:G), (((q8 ◇ q10) ◇ q9) ◇ q9) = (((q8 ◇ q7) ◇ q7) ◇ q10):=by
    intro q7 q8 q9 q10
    exact (((cg (fun t => t ◇ q10) (apc4 q7 q8 q10 q7)).symm).trans (apc4 q9 (q8 ◇ q10) q10 q7)).symm
  have apc9 : forall (q11 q12 q13:G), (((q11 ◇ q13) ◇ q12) ◇ q12) = (((q11 ◇ q11) ◇ q11) ◇ q13):=by
    intro q11 q12 q13
    exact (((cg (fun t => t ◇ q13) (apc5 q11 q11)).symm).trans ((apc6 q11 q11 q12 q13).symm)).symm
  have apc16 : forall (q14 q15 q16:G), ((((q15 ◇ q14) ◇ q15) ◇ q16) ◇ q16) = (q14 ◇ ((q15 ◇ q15) ◇ q15)):=by
    intro q14 q15 q16
    exact (((cg (fun t => q14 ◇ t) (apc5 q15 q14)).symm).trans (((cg (fun t => t ◇ ((q15 ◇ q14) ◇ q14)) ((h q14 q15 q14).symm)).symm).trans (apc4 q16 ((q15 ◇ q14) ◇ q15) ((q15 ◇ q14) ◇ q14) q14))).symm
  have apc17 : forall (q17 q18 q19:G), (q18 ◇ ((q19 ◇ q19) ◇ q19)) = (q18 ◇ ((q19 ◇ q17) ◇ q17)):=by
    intro q17 q18 q19
    exact (((cg (fun t => t ◇ ((q19 ◇ q17) ◇ q17)) ((h q18 q19 q17).symm)).symm).trans (apc16 q18 q19 ((q19 ◇ q17) ◇ q17))).symm
  have apc18 : forall (q17 q18 q19:G), (q18 ◇ ((q19 ◇ q18) ◇ q18)) = (q18 ◇ ((q19 ◇ q17) ◇ q17)):=by
    intro q17 q18 q19
    exact (((apc17 q17 q18 q19).symm).trans (apc17 q18 q18 q19)).symm
  have apc20 : forall (q20 q21:G), (q20 ◇ ((q21 ◇ q21) ◇ q21)) = (q20 ◇ ((q21 ◇ q20) ◇ q20)):=by
    intro q20 q21
    exact ((cg (fun t => q20 ◇ t) (apc5 q21 q20)).symm).trans ((apc18 q20 q20 q21).symm)
  have apc22 : forall (q22 q23:G), ((((q22 ◇ q22) ◇ q22) ◇ q23) ◇ q23) = (q22 ◇ ((q22 ◇ q22) ◇ q22)):=by
    intro q22 q23
    exact (((cg (fun t => t ◇ ((q22 ◇ q22) ◇ q22)) (apc1 q22 q22 q22)).symm).trans (apc4 q23 ((q22 ◇ q22) ◇ q22) ((q22 ◇ q22) ◇ q22) q22)).symm
  have apc23 : forall (q24 q25:G), (q25 ◇ ((q25 ◇ q25) ◇ q25)) = (q25 ◇ ((q25 ◇ q24) ◇ q24)):=by
    intro q24 q25
    exact ((apc20 q25 q25).symm).trans (apc18 q24 q25 q25)
  have apc25 : forall (q26 q27:G), (((q27 ◇ q27) ◇ q27) ◇ ((q27 ◇ q26) ◇ q26)) = q27:=by
    intro q26 q27
    exact ((cg (fun t => ((q27 ◇ q27) ◇ q27) ◇ t) (apc4 q26 q27 q27 q26)).symm).trans (apc1 q27 q26 q26)
  have apc26 : forall (q28 q29 q30 q31:G), ((((q31 ◇ q28) ◇ q30) ◇ q30) ◇ q31) = (q28 ◇ ((q31 ◇ q29) ◇ q29)):=by
    intro q28 q29 q30 q31
    exact (((cg (fun t => t ◇ ((q31 ◇ q29) ◇ q29)) ((h q28 q31 q29).symm)).symm).trans (apc6 q30 (q31 ◇ q28) ((q31 ◇ q29) ◇ q29) q31)).symm
  have apc27 : forall (q32:G), (q32 ◇ q32) = q32:=by
    intro q32
    exact (((cg (fun t => t ◇ q32) (apc9 q32 q32 ((q32 ◇ q32) ◇ q32))).trans (cg (fun t => t ◇ q32) (apc25 q32 q32))).symm).trans ((((cg (fun t => t ◇ q32) (cg (fun t => t ◇ q32) (cg (fun t => t ◇ q32) (apc23 q32 q32)))).symm).trans (apc26 ((q32 ◇ q32) ◇ q32) q32 q32 q32)).trans (apc25 q32 q32))
  have apc28 : forall (q32 q22 q23:G), ((q22 ◇ q23) ◇ q23) = q22:=by
    intro q32 q22 q23
    exact (((cg (fun t => t ◇ q23) (cg (fun t => t ◇ q23) (cg (fun t => t ◇ q22) (apc27 q22)))).trans (cg (fun t => t ◇ q23) (cg (fun t => t ◇ q23) (apc27 q22)))).symm).trans ((apc22 q22 q23).trans (((cg (fun t => q22 ◇ t) (cg (fun t => t ◇ q22) (apc27 q22))).trans (cg (fun t => q22 ◇ t) (apc27 q22))).trans (apc27 q22)))
  have apc29 : forall (q33 q34:G), q34 = q33:=by
    intro q33 q34
    exact ((((cg (fun t => (q33 ◇ (q33 ◇ q34)) ◇ t) (apc28 (((q33 ◇ q34) ◇ q33) ◇ q33) (q33 ◇ q34) q33)).trans (apc28 ((q33 ◇ (q33 ◇ q34)) ◇ (q33 ◇ q34)) q33 (q33 ◇ q34))).symm).trans (((cg (fun t => t ◇ (((q33 ◇ q34) ◇ q33) ◇ q33)) (cg (fun t => t ◇ (q33 ◇ q34)) (apc28 q33 q33 q34))).symm).trans ((h q34 (q33 ◇ q34) q33).symm))).symm
  exact (apc29 (x ◇ y) (x ◇ y)).trans ((apc29 (x ◇ y) (((y ◇ z) ◇ w) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_24247_to_4186 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_24247_to_4186
