-- Equation48042 → Equation56301
-- Recorded verdict: true
-- Premise: x * y = (y * (x * z)) * (x * x)
-- Conclusion: x * (y * z) = (w * x) * (x * u)
-- Original submission SHA-256: 8cf73091a9dd63b4715574e34177455c9c103e6644ab51d4e9d8874bc711af0e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ z)) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (w ◇ x) ◇ (x ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q2 ◇ q1))) = ((q2 ◇ q0) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q2 ◇ q2)) ((h q2 q0 q1).symm)).symm).trans ((h q2 (q0 ◇ (q2 ◇ q1)) q2).symm)).symm
  have apc1 : forall (q3 q4:G), (q4 ◇ ((q3 ◇ q4) ◇ (q3 ◇ q3))) = ((q4 ◇ q3) ◇ (q4 ◇ q4)):=by
    intro q3 q4
    exact ((cg (fun t => q4 ◇ t) (apc0 q4 q3 q3)).symm).trans (apc0 q3 (q3 ◇ q3) q4)
  have apc2 : forall (q5:G), ((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) = ((q5 ◇ q5) ◇ (q5 ◇ q5)):=by
    intro q5
    exact (((apc1 q5 q5).symm).trans (apc0 (q5 ◇ q5) q5 q5)).symm
  have apc3 : forall (q6:G), ((q6 ◇ q6) ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q6
    exact ((apc2 q6).symm).trans ((h q6 q6 q6).symm)
  have apc5 : forall (x y z:G), ((y ◇ (x ◇ z)) ◇ (x ◇ x)) = ((y ◇ (x ◇ x)) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc7 : forall (q7 q8:G), ((q8 ◇ (q7 ◇ q7)) ◇ (q7 ◇ q7)) = (q7 ◇ q8):=by
    intro q7 q8
    exact ((apc5 q7 q8 q7).symm).trans ((h q7 q8 q7).symm)
  have apc9 : forall (q9 q10:G), ((q9 ◇ q9) ◇ q10) = (q9 ◇ q10):=by
    intro q9 q10
    exact ((((cg (fun t => (q10 ◇ (q9 ◇ q9)) ◇ t) (apc3 q9)).trans (apc7 q9 q10)).symm).trans (((cg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) (cg (fun t => q10 ◇ t) (apc3 q9))).symm).trans (apc7 (q9 ◇ q9) q10))).symm
  have apc10 : forall (q11 q12:G), ((q11 ◇ q12) ◇ (q11 ◇ q11)) = (q11 ◇ (q11 ◇ q12)):=by
    intro q11 q12
    exact ((apc9 (q11 ◇ q12) (q11 ◇ q11)).symm).trans ((h q11 (q11 ◇ q12) q12).symm)
  have apc12 : forall (q13 q11 q12:G), ((q13 ◇ (q11 ◇ q12)) ◇ (q11 ◇ q11)) = (q11 ◇ (q13 ◇ q13)):=by
    intro q13 q11 q12
    exact ((cg (fun t => t ◇ (q11 ◇ q11)) (apc9 q13 (q11 ◇ q12))).symm).trans ((h q11 (q13 ◇ q13) q12).symm)
  have apc13 : forall (q0 q1 q2 q11 q12:G), (q2 ◇ (q0 ◇ (q2 ◇ q1))) = (q2 ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q11 q12
    exact (apc0 q0 q1 q2).trans (apc10 q2 q0)
  have apc15 : forall (q14 q15 q16:G), (q14 ◇ (q15 ◇ q15)) = (q14 ◇ q15):=by
    intro q14 q15 q16
    exact ((apc12 q15 q14 (q14 ◇ q16)).symm).trans (((cg (fun t => t ◇ (q14 ◇ q14)) (cg (fun t => q15 ◇ t) (apc13 q16 q16 q14 q16 q16))).symm).trans ((h q14 q15 (q16 ◇ (q14 ◇ q16))).symm))
  have apc16 : forall (q11 q12 q16 q14 q15:G), (q11 ◇ (q11 ◇ q12)) = ((q11 ◇ q12) ◇ q11):=by
    intro q11 q12 q16 q14 q15
    exact (((apc15 (q11 ◇ q12) q11 ((q11 ◇ q12) ◇ (q11 ◇ q11))).symm).trans (apc10 q11 q12)).symm
  have apc18 : forall (q17 q18:G), ((q17 ◇ q18) ◇ q18) = (q18 ◇ q17):=by
    intro q17 q18
    exact ((apc15 (q17 ◇ q18) q18 ((q17 ◇ q18) ◇ (q18 ◇ q18))).symm).trans (((cg (fun t => t ◇ (q18 ◇ q18)) (apc15 q17 q18 q17)).symm).trans ((h q18 q17 q18).symm))
  have apc19 : forall (q19 q20:G), ((q20 ◇ q19) ◇ (q19 ◇ q20)) = ((q19 ◇ q20) ◇ (q20 ◇ q19)):=by
    intro q19 q20
    exact ((((cg (fun t => (q19 ◇ q20) ◇ t) (apc18 q19 q20)).symm).trans (apc16 (q19 ◇ q20) q20 q19 q19 q19)).trans (cg (fun t => t ◇ (q19 ◇ q20)) (apc18 q19 q20))).symm
  have apc20 : forall (q21 q22 q23:G), ((q23 ◇ (q21 ◇ (q23 ◇ q22))) ◇ q23) = ((q23 ◇ q21) ◇ q23):=by
    intro q21 q22 q23
    exact (((apc16 q23 q21 (q23 ◇ (q23 ◇ q21)) (q23 ◇ (q23 ◇ q21)) (q23 ◇ (q23 ◇ q21))).symm).trans ((((cg (fun t => q23 ◇ t) ((h q23 q21 q22).symm)).symm).trans (apc13 (q21 ◇ (q23 ◇ q22)) q23 q23 q21 q21)).trans (apc16 q23 (q21 ◇ (q23 ◇ q22)) (q23 ◇ (q23 ◇ (q21 ◇ (q23 ◇ q22)))) (q23 ◇ (q23 ◇ (q21 ◇ (q23 ◇ q22)))) (q23 ◇ (q23 ◇ (q21 ◇ (q23 ◇ q22))))))).symm
  have apc22 : forall (q24 q25:G), ((q24 ◇ q25) ◇ q24) = (q24 ◇ q24):=by
    intro q24 q25
    exact ((((((cg (fun t => t ◇ q24) (cg (fun t => t ◇ q24) (apc16 q24 q25 (q24 ◇ (q24 ◇ q25)) (q24 ◇ (q24 ◇ q25)) (q24 ◇ (q24 ◇ q25))))).trans (cg (fun t => t ◇ q24) (apc18 (q24 ◇ q25) q24))).trans (cg (fun t => t ◇ q24) (apc16 q24 q25 (q24 ◇ (q24 ◇ q25)) (q24 ◇ (q24 ◇ q25)) (q24 ◇ (q24 ◇ q25))))).trans (apc18 (q24 ◇ q25) q24)).trans (apc16 q24 q25 (q24 ◇ (q24 ◇ q25)) (q24 ◇ (q24 ◇ q25)) (q24 ◇ (q24 ◇ q25)))).symm).trans ((((cg (fun t => t ◇ q24) (apc16 q24 (q24 ◇ q25) q24 q24 q24)).symm).trans (apc20 q24 q25 q24)).trans (apc9 q24 q24))
  have apc23 : forall (q26 q27:G), ((q27 ◇ q26) ◇ (q27 ◇ q26)) = (q27 ◇ (q27 ◇ q26)):=by
    intro q26 q27
    exact (((apc9 q27 (q27 ◇ q26)).symm).trans (((cg (fun t => t ◇ (q27 ◇ q26)) (apc22 q27 q26)).symm).trans (apc22 (q27 ◇ q26) q27))).symm
  have apc24 : forall (q28 q29:G), ((q28 ◇ q29) ◇ (q29 ◇ q28)) = (q29 ◇ (q29 ◇ q28)):=by
    intro q28 q29
    exact ((((cg (fun t => (q29 ◇ q28) ◇ t) (apc18 q28 q29)).trans (apc23 q28 q29)).symm).trans ((((cg (fun t => t ◇ ((q28 ◇ q29) ◇ q29)) (apc18 q28 q29)).symm).trans (apc23 q29 (q28 ◇ q29))).trans (cg (fun t => (q28 ◇ q29) ◇ t) (apc18 q28 q29)))).symm
  have apc25 : forall (q19 q20 q28 q29:G), (q20 ◇ (q20 ◇ q19)) = (q19 ◇ (q19 ◇ q20)):=by
    intro q19 q20 q28 q29
    exact (((apc24 q20 q19).symm).trans ((apc19 q19 q20).trans (apc24 q19 q20))).symm
  have apc27 : forall (q30 q31:G), (q31 ◇ q30) = (q30 ◇ q31):=by
    intro q30 q31
    exact (((((cg (fun t => t ◇ (q30 ◇ q30)) (apc15 (q31 ◇ q30) q31 ((q31 ◇ q30) ◇ (q31 ◇ q31)))).trans (cg (fun t => t ◇ (q30 ◇ q30)) (apc22 q31 q30))).trans (apc9 q31 (q30 ◇ q30))).trans (apc15 q31 q30 (q31 ◇ (q30 ◇ q30)))).symm).trans (((cg (fun t => t ◇ (q30 ◇ q30)) (apc0 q30 q30 q31)).symm).trans ((h q30 q31 (q31 ◇ q30)).symm))
  have apc28 : forall (q19 q20 q28 q29 q26 q27:G), ((q26 ◇ q27) ◇ (q26 ◇ q27)) = (q26 ◇ q26):=by
    intro q19 q20 q28 q29 q26 q27
    exact (((cg (fun t => t ◇ (q27 ◇ q26)) (apc27 q26 q27)).trans (cg (fun t => (q26 ◇ q27) ◇ t) (apc27 q26 q27))).symm).trans (((apc23 q26 q27).trans (apc25 q26 q27 (q27 ◇ (q27 ◇ q26)) (q27 ◇ (q27 ◇ q26)))).trans ((apc27 (q26 ◇ q27) q26).trans (apc22 q26 q27)))
  have apc32 : forall (q32 q33 q34:G), ((q32 ◇ q33) ◇ q34) = (q32 ◇ q32):=by
    intro q32 q33 q34
    exact (((((((((cg (fun t => t ◇ ((q32 ◇ q33) ◇ (q32 ◇ q33))) (apc27 (q32 ◇ q32) q34)).trans (cg (fun t => t ◇ ((q32 ◇ q33) ◇ (q32 ◇ q33))) (apc9 q32 q34))).trans (cg (fun t => (q32 ◇ q34) ◇ t) (apc28 ((q32 ◇ q33) ◇ (q32 ◇ q33)) ((q32 ◇ q33) ◇ (q32 ◇ q33)) ((q32 ◇ q33) ◇ (q32 ◇ q33)) ((q32 ◇ q33) ◇ (q32 ◇ q33)) q32 q33))).trans (apc27 (q32 ◇ q32) (q32 ◇ q34))).trans (apc9 q32 (q32 ◇ q34))).trans (apc27 (q32 ◇ q34) q32)).trans (apc22 q32 q34)).symm).trans (((cg (fun t => t ◇ ((q32 ◇ q33) ◇ (q32 ◇ q33))) (cg (fun t => q34 ◇ t) (apc28 q32 q32 q32 q32 q32 q33))).symm).trans ((h (q32 ◇ q33) q34 (q32 ◇ q33)).symm))).symm
  have apc33 : forall (q35 q30 q31:G), (q30 ◇ q31) = (q35 ◇ q35):=by
    intro q35 q30 q31
    exact (((((((cg (fun t => t ◇ (q30 ◇ q30)) (cg (fun t => q31 ◇ t) (cg (fun t => t ◇ (q30 ◇ q30)) (apc27 q35 q30)))).trans (cg (fun t => t ◇ (q30 ◇ q30)) (cg (fun t => q31 ◇ t) (apc32 q35 q30 (q30 ◇ q30))))).trans (cg (fun t => t ◇ (q30 ◇ q30)) (apc27 (q35 ◇ q35) q31))).trans (cg (fun t => t ◇ (q30 ◇ q30)) (apc32 q35 q35 q31))).trans (apc32 q35 q35 (q30 ◇ q30))).symm).trans (((cg (fun t => t ◇ (q30 ◇ q30)) (cg (fun t => q31 ◇ t) (apc0 q35 q35 q30))).symm).trans ((h q30 q31 (q35 ◇ (q30 ◇ q35))).symm))).symm
  exact (apc33 (x ◇ (y ◇ z)) x (y ◇ z)).trans ((apc33 (x ◇ (y ◇ z)) (w ◇ x) (x ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48042_to_56301 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48042_to_56301
