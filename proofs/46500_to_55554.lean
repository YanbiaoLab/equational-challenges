-- Equation46500 → Equation55554
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (x * (y * x))
-- Conclusion: x * (y * z) = w * ((u * v) * x)
-- Original submission SHA-256: 9faaefe64a373564d1d53c3bebd0d321678b6abdba83e4c4413704f2f21dcefb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (x ◇ (y ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ z) = w ◇ ((u ◇ v) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) ((h q0 q0 q0).symm)).symm).trans ((h (q0 ◇ q0) q0 q1).symm)
  have apc1 : forall (q2:G), (((q2 ◇ q2) ◇ q2) ◇ ((q2 ◇ q2) ◇ q2)) = ((q2 ◇ q2) ◇ q2):=by
    intro q2
    exact ((cg (fun t => ((q2 ◇ q2) ◇ q2) ◇ t) (apc0 q2 q2)).symm).trans ((((cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (apc0 q2 q2)).symm).trans (apc0 (q2 ◇ q2) (q2 ◇ q2))).trans ((cg (fun t => t ◇ (q2 ◇ q2)) (apc0 q2 q2)).trans (apc0 q2 (q2 ◇ q2))))
  have apc2 : forall (q3 q4:G), ((q4 ◇ (q3 ◇ q3)) ◇ ((q3 ◇ q3) ◇ q3)) = ((q3 ◇ q3) ◇ q3):=by
    intro q3 q4
    exact (((cg (fun t => (q4 ◇ (q3 ◇ q3)) ◇ t) (apc0 q3 q3)).symm).trans (apc0 (q3 ◇ q3) q4)).trans ((cg (fun t => t ◇ (q3 ◇ q3)) (apc0 q3 q3)).trans (apc0 q3 (q3 ◇ q3)))
  have apc3 : forall (q5 q6:G), ((q6 ◇ ((q5 ◇ q5) ◇ q5)) ◇ ((q5 ◇ q5) ◇ q5)) = ((q5 ◇ q5) ◇ q5):=by
    intro q5 q6
    exact ((cg (fun t => (q6 ◇ ((q5 ◇ q5) ◇ q5)) ◇ t) (apc1 q5)).symm).trans ((((cg (fun t => (q6 ◇ ((q5 ◇ q5) ◇ q5)) ◇ t) (cg (fun t => ((q5 ◇ q5) ◇ q5) ◇ t) (apc1 q5))).symm).trans ((h ((q5 ◇ q5) ◇ q5) ((q5 ◇ q5) ◇ q5) q6).symm)).trans (apc1 q5))
  have apc4 : forall (x y z:G), ((z ◇ y) ◇ (x ◇ (y ◇ x))) = ((x ◇ y) ◇ (x ◇ (y ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc5 : forall (q7 q8:G), ((q7 ◇ q8) ◇ (q7 ◇ (q8 ◇ q7))) = (q7 ◇ q8):=by
    intro q7 q8
    exact ((apc4 q7 q8 q7).symm).trans ((h q7 q8 q7).symm)
  have apc6 : forall (q9 q10:G), (((q9 ◇ q9) ◇ q9) ◇ (q10 ◇ ((q9 ◇ q9) ◇ q10))) = (q10 ◇ (q9 ◇ q9)):=by
    intro q9 q10
    exact ((cg (fun t => t ◇ (q10 ◇ ((q9 ◇ q9) ◇ q10))) (apc0 q9 q9)).symm).trans ((h q10 (q9 ◇ q9) (q9 ◇ q9)).symm)
  have apc8 : forall (q11 q12 q13:G), ((q11 ◇ q12) ◇ (q13 ◇ ((q11 ◇ (q12 ◇ q11)) ◇ q13))) = (q13 ◇ (q11 ◇ (q12 ◇ q11))):=by
    intro q11 q12 q13
    exact ((cg (fun t => t ◇ (q13 ◇ ((q11 ◇ (q12 ◇ q11)) ◇ q13))) ((h q11 q12 q11).symm)).symm).trans ((h q13 (q11 ◇ (q12 ◇ q11)) (q11 ◇ q12)).symm)
  have apc9 : forall (q14:G), (q14 ◇ (q14 ◇ q14)) = ((q14 ◇ q14) ◇ q14):=by
    intro q14
    exact ((((cg (fun t => (q14 ◇ (q14 ◇ q14)) ◇ t) (apc1 q14)).trans (apc2 q14 q14)).symm).trans ((((cg (fun t => (q14 ◇ (q14 ◇ q14)) ◇ t) (cg (fun t => ((q14 ◇ q14) ◇ q14) ◇ t) (apc3 q14 q14))).symm).trans (apc8 q14 (q14 ◇ q14) ((q14 ◇ q14) ◇ q14))).trans (apc6 q14 q14))).symm
  have apc10 : forall (q15:G), ((q15 ◇ q15) ◇ ((q15 ◇ q15) ◇ q15)) = (q15 ◇ q15):=by
    intro q15
    exact ((cg (fun t => (q15 ◇ q15) ◇ t) (apc9 q15)).symm).trans (apc5 q15 q15)
  have apc11 : forall (q16:G), ((q16 ◇ q16) ◇ q16) = (q16 ◇ q16):=by
    intro q16
    exact ((((cg (fun t => (q16 ◇ q16) ◇ t) (apc1 q16)).trans (apc10 q16)).symm).trans ((((cg (fun t => t ◇ (((q16 ◇ q16) ◇ q16) ◇ ((q16 ◇ q16) ◇ q16))) (apc10 q16)).symm).trans (apc0 ((q16 ◇ q16) ◇ q16) (q16 ◇ q16))).trans ((cg (fun t => t ◇ ((q16 ◇ q16) ◇ q16)) (apc1 q16)).trans (apc1 q16)))).symm
  have apc12 : forall (q14:G), (q14 ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q14
    exact (apc9 q14).trans (apc11 q14)
  have apc15 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact (apc0 q0 q1).trans (apc11 q0)
  have apc17 : forall (q9 q17 q18:G), ((q18 ◇ (q17 ◇ q9)) ◇ (q9 ◇ q9)) = ((q9 ◇ q9) ◇ (q17 ◇ q9)):=by
    intro q9 q17 q18
    exact (((cg (fun t => (q18 ◇ (q17 ◇ q9)) ◇ t) (cg (fun t => (q9 ◇ q9) ◇ t) (apc11 q9))).trans (cg (fun t => (q18 ◇ (q17 ◇ q9)) ◇ t) (apc15 q9 q9))).symm).trans (((cg (fun t => (q18 ◇ (q17 ◇ q9)) ◇ t) (cg (fun t => (q9 ◇ q9) ◇ t) (apc0 q9 q17))).symm).trans ((h (q9 ◇ q9) (q17 ◇ q9) q18).symm))
  have apc18 : forall (q19 q20:G), ((q19 ◇ q19) ◇ (q20 ◇ q19)) = (q19 ◇ q19):=by
    intro q19 q20
    exact (((cg (fun t => ((q19 ◇ q19) ◇ (q20 ◇ q19)) ◇ t) (apc15 q19 q19)).trans (apc17 q19 q20 (q19 ◇ q19))).symm).trans ((((cg (fun t => t ◇ ((q19 ◇ q19) ◇ (q19 ◇ q19))) (apc17 q19 q20 q19)).symm).trans (apc15 (q19 ◇ q19) (q19 ◇ (q20 ◇ q19)))).trans (apc15 q19 q19))
  have apc19 : forall (q21 q22:G), ((q21 ◇ q21) ◇ (q22 ◇ (q21 ◇ q21))) = (q21 ◇ q21):=by
    intro q21 q22
    exact (((cg (fun t => t ◇ (q22 ◇ (q21 ◇ q21))) (apc15 q21 q21)).symm).trans (apc18 (q21 ◇ q21) q22)).trans (apc15 q21 q21)
  have apc20 : forall (q23 q24 q25:G), ((q25 ◇ q24) ◇ (q23 ◇ q23)) = ((q23 ◇ q23) ◇ q24):=by
    intro q23 q24 q25
    exact ((cg (fun t => (q25 ◇ q24) ◇ t) (apc19 q23 q24)).symm).trans ((h (q23 ◇ q23) q24 q25).symm)
  have apc21 : forall (q26 q27:G), ((q27 ◇ q27) ◇ q26) = ((q26 ◇ q26) ◇ q27):=by
    intro q26 q27
    exact (((apc20 q26 q27 q27).symm).trans ((((cg (fun t => t ◇ (q26 ◇ q26)) (apc12 q27)).symm).trans (apc20 q26 (q27 ◇ q27) q27)).trans (apc20 q27 q26 q26))).symm
  have apc22 : forall (q28 q29:G), ((q28 ◇ (q29 ◇ q28)) ◇ (q28 ◇ (q29 ◇ q28))) = ((q29 ◇ q29) ◇ (q28 ◇ (q29 ◇ q28))):=by
    intro q28 q29
    exact ((((apc20 (q28 ◇ (q29 ◇ q28)) q29 q28).trans (apc21 q29 (q28 ◇ (q29 ◇ q28)))).symm).trans ((((cg (fun t => t ◇ ((q28 ◇ (q29 ◇ q28)) ◇ (q28 ◇ (q29 ◇ q28)))) ((h q28 q29 q28).symm)).symm).trans (apc0 (q28 ◇ (q29 ◇ q28)) (q28 ◇ q29))).trans (apc11 (q28 ◇ (q29 ◇ q28))))).symm
  have apc23 : forall (q30 q31:G), ((q30 ◇ q30) ◇ q31) = (q30 ◇ q30):=by
    intro q30 q31
    exact ((((cg (fun t => (q30 ◇ q30) ◇ t) (apc19 q30 q31)).trans (apc18 q30 q30)).symm).trans ((((cg (fun t => t ◇ ((q30 ◇ q30) ◇ (q31 ◇ (q30 ◇ q30)))) (apc19 q30 q31)).symm).trans (apc22 (q30 ◇ q30) q31)).trans ((cg (fun t => (q31 ◇ q31) ◇ t) (apc19 q30 q31)).trans (apc20 q30 q31 q31)))).symm
  have apc25 : forall (q32 q33 q34:G), (q33 ◇ q34) = (q32 ◇ q32):=by
    intro q32 q33 q34
    exact (((apc23 q32 (q33 ◇ (q34 ◇ q33))).symm).trans (((cg (fun t => t ◇ (q33 ◇ (q34 ◇ q33))) (apc23 q32 q34)).symm).trans ((h q33 q34 (q32 ◇ q32)).symm))).symm
  exact (apc25 (x ◇ (y ◇ z)) x (y ◇ z)).trans ((apc25 (x ◇ (y ◇ z)) w ((u ◇ v) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46500_to_55554 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46500_to_55554
