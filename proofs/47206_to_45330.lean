-- Equation47206 → Equation45330
-- Recorded verdict: true
-- Premise: x * y = (y * y) * ((z * y) * x)
-- Conclusion: x * y = x * (((z * x) * w) * u)
-- Original submission SHA-256: c6cc71ca1a045e1ca0a0058cb6d0c97f01f02d6c5ef0f67bbeea875797272230
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ y) ◇ ((z ◇ y) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = x ◇ (((z ◇ x) ◇ w) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q2) ◇ q0) ◇ q2) = ((q2 ◇ q2) ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q2 ◇ q2) ◇ t) ((h q0 q2 q1).symm)).symm).trans ((h ((q1 ◇ q2) ◇ q0) q2 q2).symm)).symm
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ q5) ◇ (((q5 ◇ q5) ◇ (q3 ◇ q5)) ◇ q4)) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact ((cg (fun t => (q5 ◇ q5) ◇ t) (cg (fun t => t ◇ q4) (apc0 q3 q3 q5))).symm).trans ((h q4 q5 ((q3 ◇ q5) ◇ q3)).symm)
  have apc2 : forall (q6 q7:G), ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ q6)) = (q6 ◇ q7):=by
    intro q6 q7
    exact ((cg (fun t => (q7 ◇ q7) ◇ t) (cg (fun t => t ◇ q6) ((h q7 q7 q6).symm))).symm).trans (apc1 (q6 ◇ q7) q6 q7)
  have apc3 : forall (q4 q5:G), ((q5 ◇ q5) ◇ ((q4 ◇ q4) ◇ (q5 ◇ q4))) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((cg (fun t => (q5 ◇ q5) ◇ t) (apc0 q5 q4 q4)).symm).trans ((h q4 q5 (q4 ◇ q4)).symm)
  have apc4 : forall (q8:G), ((q8 ◇ q8) ◇ q8) = (q8 ◇ q8):=by
    intro q8
    exact (((apc3 q8 q8).symm).trans ((h (q8 ◇ q8) q8 q8).symm)).symm
  have apc5 : forall (x y z:G), ((y ◇ y) ◇ ((z ◇ y) ◇ x)) = ((y ◇ y) ◇ ((x ◇ y) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc6 : forall (x y z q6 q7:G), ((q7 ◇ q7) ◇ ((q6 ◇ q7) ◇ q6)) = (q6 ◇ q7):=by
    intro x y z q6 q7
    exact ((apc5 q6 q7 q7).symm).trans (apc2 q6 q7)
  have apc7 : forall (q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = (q9 ◇ q9):=by
    intro q9
    exact ((cg (fun t => (q9 ◇ q9) ◇ t) (apc4 q9)).symm).trans ((h q9 q9 q9).symm)
  have apc8 : forall (q10 q11:G), ((q10 ◇ q10) ◇ ((q10 ◇ q10) ◇ q11)) = (q11 ◇ (q10 ◇ q10)):=by
    intro q10 q11
    exact ((cg (fun t => t ◇ ((q10 ◇ q10) ◇ q11)) (apc7 q10)).symm).trans (((cg (fun t => ((q10 ◇ q10) ◇ (q10 ◇ q10)) ◇ t) (cg (fun t => t ◇ q11) (apc7 q10))).symm).trans ((h q11 (q10 ◇ q10) (q10 ◇ q10)).symm))
  have apc9 : forall (q12 q13:G), (q12 ◇ (q13 ◇ q13)) = (q12 ◇ q13):=by
    intro q12 q13
    exact ((apc8 q13 q12).symm).trans ((h q12 q13 q13).symm)
  have apc15 : forall (q14 q15:G), ((q14 ◇ q14) ◇ q15) = (q14 ◇ q15):=by
    intro q14 q15
    exact ((((cg (fun t => (q15 ◇ q15) ◇ t) (apc0 q15 q14 q14)).trans (apc3 q14 q15)).symm).trans (((cg (fun t => (q15 ◇ q15) ◇ t) (apc9 ((q14 ◇ q14) ◇ q15) q14)).symm).trans (apc6 q14 q14 q14 (q14 ◇ q14) q15))).symm
  have apc17 : forall (q16 q17 q18:G), (q17 ◇ ((q18 ◇ q17) ◇ q16)) = (q16 ◇ q17):=by
    intro q16 q17 q18
    exact ((apc15 q17 ((q18 ◇ q17) ◇ q16)).symm).trans ((h q16 q17 q18).symm)
  have apc18 : forall (q16 q17:G), (q17 ◇ (q17 ◇ q16)) = (q16 ◇ q17):=by
    intro q16 q17
    exact ((apc15 q17 (q17 ◇ q16)).symm).trans (((cg (fun t => (q17 ◇ q17) ◇ t) (apc15 q17 q16)).symm).trans ((h q16 q17 q17).symm))
  have apc20 : forall (q19 q20 q21:G), (q21 ◇ (((q20 ◇ q21) ◇ q19) ◇ q21)) = ((q19 ◇ q21) ◇ q21):=by
    intro q19 q20 q21
    exact ((((cg (fun t => t ◇ q21) ((h q19 q21 q20).symm)).symm).trans (apc0 ((q20 ◇ q21) ◇ q19) q21 q21)).trans (apc15 q21 (((q20 ◇ q21) ◇ q19) ◇ q21))).symm
  have apc21 : forall (q22 q23:G), (q23 ◇ ((q23 ◇ q22) ◇ q23)) = ((q22 ◇ q23) ◇ q23):=by
    intro q22 q23
    exact ((cg (fun t => q23 ◇ t) (cg (fun t => t ◇ q23) (apc15 q23 q22))).symm).trans (apc20 q22 q23 q23)
  have apc22 : forall (q14 q15 q4 q5:G), (q5 ◇ (q4 ◇ (q5 ◇ q4))) = (q4 ◇ q5):=by
    intro q14 q15 q4 q5
    exact (((cg (fun t => (q5 ◇ q5) ◇ t) (apc15 q4 (q5 ◇ q4))).trans (apc15 q5 (q4 ◇ (q5 ◇ q4)))).symm).trans (apc3 q4 q5)
  have apc23 : forall (q24 q25:G), ((q25 ◇ q24) ◇ ((q24 ◇ q25) ◇ q25)) = (q24 ◇ q25):=by
    intro q24 q25
    exact (((cg (fun t => (q25 ◇ q24) ◇ t) (apc21 q24 q25)).symm).trans (apc22 q24 q24 q25 (q25 ◇ q24))).trans (apc18 q24 q25)
  have apc24 : forall (q26 q27:G), (q27 ◇ (q26 ◇ q27)) = ((q26 ◇ q27) ◇ q27):=by
    intro q26 q27
    exact (((apc17 (q26 ◇ q27) q27 q26).symm).trans (apc9 q27 (q26 ◇ q27))).symm
  have apc26 : forall (q14 q15 q26 q27 q4 q5:G), (q5 ◇ ((q5 ◇ q4) ◇ q4)) = (q4 ◇ q5):=by
    intro q14 q15 q26 q27 q4 q5
    exact ((cg (fun t => q5 ◇ t) (apc24 q5 q4)).symm).trans (apc22 q14 q15 q4 q5)
  have apc31 : forall (q28 q29:G), ((q28 ◇ q29) ◇ q29) = (q29 ◇ q29):=by
    intro q28 q29
    exact (((apc17 q29 q29 q28).symm).trans (((cg (fun t => q29 ◇ t) (apc24 q28 q29)).symm).trans (apc18 (q28 ◇ q29) q29))).symm
  have apc32 : forall (q14 q15 q26 q27 q4 q5 q28 q29:G), (q5 ◇ q4) = (q4 ◇ q5):=by
    intro q14 q15 q26 q27 q4 q5 q28 q29
    exact ((apc9 q5 q4).symm).trans (((cg (fun t => q5 ◇ t) (apc31 q5 q4)).symm).trans (apc26 q14 q15 q26 q27 q4 q5))
  have apc33 : forall (q24 q25 q28 q29:G), ((q24 ◇ q25) ◇ (q25 ◇ q25)) = (q24 ◇ q25):=by
    intro q24 q25 q28 q29
    exact ((cg (fun t => t ◇ (q25 ◇ q25)) (apc32 (q25 ◇ q24) (q25 ◇ q24) (q25 ◇ q24) (q25 ◇ q24) q24 q25 (q25 ◇ q24) (q25 ◇ q24))).symm).trans (((cg (fun t => (q25 ◇ q24) ◇ t) (apc31 q24 q25)).symm).trans (apc23 q24 q25))
  have apc34 : forall (q30 q31:G), (q31 ◇ q31) = (q30 ◇ q31):=by
    intro q30 q31
    exact ((((apc33 q30 q31 q30 q30).symm).trans (apc32 q30 q30 q30 q30 (q31 ◇ q31) (q30 ◇ q31) q30 q30)).trans (((apc15 q31 (q30 ◇ q31)).trans (apc32 (q31 ◇ (q30 ◇ q31)) (q31 ◇ (q30 ◇ q31)) (q31 ◇ (q30 ◇ q31)) (q31 ◇ (q30 ◇ q31)) (q30 ◇ q31) q31 (q31 ◇ (q30 ◇ q31)) (q31 ◇ (q30 ◇ q31)))).trans (apc31 q30 q31))).symm
  have apc35 : forall (q32 q33:G), (q32 ◇ q33) = (q32 ◇ q32):=by
    intro q32 q33
    exact ((apc34 q33 q32).trans (apc32 q32 q32 q32 q32 q32 q33 q32 q32)).symm
  exact (apc35 x y).trans ((apc35 x (((z ◇ x) ◇ w) ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47206_to_45330 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47206_to_45330
