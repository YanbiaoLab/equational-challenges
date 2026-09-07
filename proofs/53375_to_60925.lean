-- Equation53375 → Equation60925
-- Recorded verdict: true
-- Premise: x * y = (((y * z) * y) * x) * x
-- Conclusion: (x * x) * y = (y * (y * y)) * x
-- Original submission SHA-256: 16cd607477de2543adcd14c4373bd94efd7d2eee4527af4a741e57674721ffa6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((y ◇ z) ◇ y) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = (y ◇ (y ◇ y)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((((y ◇ z) ◇ y) ◇ x) ◇ x) = ((((y ◇ x) ◇ y) ◇ x) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((((q1 ◇ q0) ◇ q1) ◇ q0) ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3:G), (((q3 ◇ q2) ◇ q3) ◇ (q3 ◇ q2)) = ((q3 ◇ q2) ◇ (q3 ◇ q2)):=by
    intro q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ q2)) ((h (q3 ◇ q2) q3 q2).symm)).symm).trans ((h (q3 ◇ q2) (q3 ◇ q2) q3).symm)
  have apc3 : forall (q4 q5:G), (((q4 ◇ q5) ◇ (q4 ◇ q5)) ◇ (q4 ◇ q5)) = ((q4 ◇ q5) ◇ q4):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ (q4 ◇ q5)) (apc2 q5 q4)).symm).trans ((h (q4 ◇ q5) q4 q5).symm)
  have apc4 : forall (q6 q7:G), ((q6 ◇ q7) ◇ (q6 ◇ q7)) = ((q6 ◇ q7) ◇ q6):=by
    intro q6 q7
    exact ((((cg (fun t => t ◇ (q6 ◇ q7)) (apc2 q7 q6)).trans (apc3 q6 q7)).symm).trans (((cg (fun t => t ◇ (q6 ◇ q7)) (cg (fun t => t ◇ (q6 ◇ q7)) (apc3 q6 q7))).symm).trans (apc1 (q6 ◇ q7) (q6 ◇ q7)))).symm
  have apc5 : forall (q8 q2 q9:G), (((((q8 ◇ q2) ◇ q8) ◇ q8) ◇ q9) ◇ q9) = (q9 ◇ ((q8 ◇ q2) ◇ q8)):=by
    intro q8 q2 q9
    exact ((cg (fun t => t ◇ q9) (cg (fun t => t ◇ q9) ((h ((q8 ◇ q2) ◇ q8) q8 q2).symm))).symm).trans ((h q9 ((q8 ◇ q2) ◇ q8) ((q8 ◇ q2) ◇ q8)).symm)
  have apc6 : forall (q10 q11:G), (q11 ◇ ((q11 ◇ q10) ◇ q11)) = ((q11 ◇ q11) ◇ q11):=by
    intro q10 q11
    exact (((cg (fun t => t ◇ q11) ((h q11 q11 q10).symm)).symm).trans (apc5 q11 q10 q11)).symm
  have apc7 : forall (q12 q13:G), (((q12 ◇ q13) ◇ q12) ◇ (q12 ◇ q13)) = (((q12 ◇ q13) ◇ q12) ◇ q12):=by
    intro q12 q13
    exact ((apc3 (q12 ◇ q13) q12).symm).trans ((h ((q12 ◇ q13) ◇ q12) q12 q13).symm)
  have apc8 : forall (q14 q15:G), (q15 ◇ (q15 ◇ q14)) = ((q15 ◇ q15) ◇ q15):=by
    intro q14 q15
    exact ((((apc5 q15 q14 q15).trans (apc6 q14 q15)).symm).trans (((cg (fun t => t ◇ q15) (cg (fun t => t ◇ q15) (apc7 q15 q14))).symm).trans (apc1 q15 (q15 ◇ q14)))).symm
  have apc9 : forall (q16 q17:G), ((q17 ◇ q16) ◇ ((q17 ◇ q17) ◇ q17)) = ((q17 ◇ q16) ◇ q17):=by
    intro q16 q17
    exact ((apc5 q17 q17 (q17 ◇ q16)).symm).trans (((cg (fun t => t ◇ (q17 ◇ q16)) (cg (fun t => t ◇ (q17 ◇ q16)) (cg (fun t => t ◇ q17) (apc8 q16 q17)))).symm).trans (apc1 (q17 ◇ q16) q17))
  have apc11 : forall (q18:G), (((q18 ◇ q18) ◇ q18) ◇ q18) = ((q18 ◇ q18) ◇ q18):=by
    intro q18
    exact ((((apc9 q18 q18).symm).trans (apc8 q18 (q18 ◇ q18))).trans ((cg (fun t => t ◇ (q18 ◇ q18)) (apc4 q18 q18)).trans (apc7 q18 q18))).symm
  have apc12 : forall (q19:G), ((q19 ◇ q19) ◇ q19) = (q19 ◇ q19):=by
    intro q19
    exact ((apc11 q19).symm).trans (((cg (fun t => t ◇ q19) (apc11 q19)).symm).trans ((h q19 q19 q19).symm))
  have apc14 : forall (q20 q21:G), (((q20 ◇ q21) ◇ q20) ◇ q20) = ((q20 ◇ q21) ◇ q20):=by
    intro q20 q21
    exact ((apc7 q20 q21).symm).trans ((((cg (fun t => t ◇ (q20 ◇ q21)) (apc4 q20 q21)).symm).trans (apc12 (q20 ◇ q21))).trans (apc4 q20 q21))
  have apc15 : forall (q22 q23:G), ((q22 ◇ q23) ◇ q22) = (q22 ◇ q22):=by
    intro q22 q23
    exact ((apc14 q22 q23).symm).trans (((cg (fun t => t ◇ q22) (apc14 q22 q23)).symm).trans ((h q22 q22 q23).symm))
  have apc17 : forall (q24 q25:G), (((q25 ◇ q25) ◇ q24) ◇ q24) = (q24 ◇ q25):=by
    intro q24 q25
    exact ((cg (fun t => t ◇ q24) (cg (fun t => t ◇ q24) (apc12 q25))).symm).trans ((h q24 q25 q25).symm)
  have apc19 : forall (q22 q23 q6 q7:G), ((q6 ◇ q7) ◇ (q6 ◇ q7)) = (q6 ◇ q6):=by
    intro q22 q23 q6 q7
    exact (apc4 q6 q7).trans (apc15 q6 q7)
  have apc20 : forall (q26 q27:G), (q27 ◇ q27) = (q26 ◇ q26):=by
    intro q26 q27
    exact (((cg (fun t => (q27 ◇ q26) ◇ t) (apc17 q27 q26)).trans (apc19 ((q27 ◇ q26) ◇ (q27 ◇ q26)) ((q27 ◇ q26) ◇ (q27 ◇ q26)) q27 q26)).symm).trans ((((cg (fun t => t ◇ (((q26 ◇ q26) ◇ q27) ◇ q27)) (apc17 q27 q26)).symm).trans (apc19 q26 q26 ((q26 ◇ q26) ◇ q27) q27)).trans ((apc19 (((q26 ◇ q26) ◇ q27) ◇ ((q26 ◇ q26) ◇ q27)) (((q26 ◇ q26) ◇ q27) ◇ ((q26 ◇ q26) ◇ q27)) (q26 ◇ q26) q27).trans (apc19 ((q26 ◇ q26) ◇ (q26 ◇ q26)) ((q26 ◇ q26) ◇ (q26 ◇ q26)) q26 q26)))
  have apc21 : forall (q28 q0 q29:G), (q0 ◇ (q28 ◇ q28)) = (q0 ◇ q28):=by
    intro q28 q0 q29
    exact (((((((((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((q28 ◇ q29) ◇ q28)) (cg (fun t => t ◇ ((q28 ◇ q29) ◇ q28)) (cg (fun t => t ◇ q28) (cg (fun t => q28 ◇ t) (apc15 q28 q29))))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((q28 ◇ q29) ◇ q28)) (cg (fun t => ((q28 ◇ (q28 ◇ q28)) ◇ q28) ◇ t) (apc15 q28 q29)))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((q28 ◇ q29) ◇ q28)) (cg (fun t => t ◇ (q28 ◇ q28)) (apc15 q28 (q28 ◇ q28))))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => ((q28 ◇ q28) ◇ (q28 ◇ q28)) ◇ t) (apc15 q28 q29))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ (q28 ◇ q28)) (apc19 ((q28 ◇ q28) ◇ (q28 ◇ q28)) ((q28 ◇ q28) ◇ (q28 ◇ q28)) q28 q28))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (apc19 ((q28 ◇ q28) ◇ (q28 ◇ q28)) ((q28 ◇ q28) ◇ (q28 ◇ q28)) q28 q28)))).trans (apc17 q0 q28)).symm).trans ((((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (apc0 ((q28 ◇ q29) ◇ q28) q28 q29))).symm).trans ((h q0 ((q28 ◇ q29) ◇ q28) ((q28 ◇ q29) ◇ q28)).symm)).trans (cg (fun t => q0 ◇ t) (apc15 q28 q29)))).symm
  have apc22 : forall (q30 q31:G), ((q30 ◇ q30) ◇ q31) = (q30 ◇ q31):=by
    intro q30 q31
    exact ((((cg (fun t => t ◇ q30) (apc21 q30 (q31 ◇ q31) ((q31 ◇ q31) ◇ (q30 ◇ q30)))).trans (apc17 q30 q31)).symm).trans (((apc21 q30 ((q31 ◇ q31) ◇ (q30 ◇ q30)) q30).symm).trans (apc17 (q30 ◇ q30) q31))).symm
  have apc24 : forall (q32 q33 q34:G), ((q32 ◇ q33) ◇ q34) = (q32 ◇ q34):=by
    intro q32 q33 q34
    exact (((apc22 q32 q34).symm).trans (((cg (fun t => t ◇ q34) (apc19 q32 q32 q32 q33)).symm).trans (apc22 (q32 ◇ q33) q34))).symm
  have apc25 : forall (q35 q36 q37:G), (q36 ◇ q37) = (q35 ◇ q36):=by
    intro q35 q36 q37
    exact ((((cg (fun t => t ◇ q36) (apc24 q35 q35 q36)).trans (apc24 q35 q36 q36)).symm).trans (((cg (fun t => t ◇ q36) (cg (fun t => t ◇ q36) (apc20 q35 q37))).symm).trans (apc17 q36 q37))).symm
  exact (apc25 x (x ◇ x) y).trans (apc25 (y ◇ (y ◇ y)) x (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53375_to_60925 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53375_to_60925
