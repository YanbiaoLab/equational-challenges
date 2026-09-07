-- Equation18127 → Equation19390
-- Recorded verdict: true
-- Premise: x = (y * x) * (z * ((x * x) * x))
-- Conclusion: x = (y * z) * ((z * x) * (y * x))
-- Original submission SHA-256: 3b6da69ece36c4742e55c6c92e6cabb23051ff4f2cbf6a91ed019760fe901447
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (z ◇ ((x ◇ x) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ x) ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q1 ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) ((h q0 q0 (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))).symm)).symm).trans ((h ((q0 ◇ q0) ◇ q0) q1 (q0 ◇ q0)).symm)
  have apc5 : forall (q2:G), ((((q2 ◇ q2) ◇ q2) ◇ ((q2 ◇ q2) ◇ q2)) ◇ ((q2 ◇ q2) ◇ q2)) = (q2 ◇ ((q2 ◇ q2) ◇ q2)):=by
    intro q2
    exact (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ q2)) ((h q2 q2 (((q2 ◇ q2) ◇ q2) ◇ ((q2 ◇ q2) ◇ q2))).symm)).symm).trans (apc0 ((q2 ◇ q2) ◇ q2) (q2 ◇ q2))).symm
  have apc6 : forall (q3 q4:G), ((q4 ◇ q3) ◇ (q3 ◇ ((q3 ◇ q3) ◇ q3))) = q3:=by
    intro q3 q4
    exact ((cg (fun t => (q4 ◇ q3) ◇ t) (apc5 q3)).symm).trans ((h q3 q4 (((q3 ◇ q3) ◇ q3) ◇ ((q3 ◇ q3) ◇ q3))).symm)
  have apc8 : forall (q5 q6:G), ((q5 ◇ ((q5 ◇ q5) ◇ q5)) ◇ (q6 ◇ (q5 ◇ ((q5 ◇ q5) ◇ q5)))) = ((q5 ◇ q5) ◇ q5):=by
    intro q5 q6
    exact ((cg (fun t => (q5 ◇ ((q5 ◇ q5) ◇ q5)) ◇ t) (cg (fun t => q6 ◇ t) (apc5 q5))).symm).trans (((cg (fun t => t ◇ (q6 ◇ ((((q5 ◇ q5) ◇ q5) ◇ ((q5 ◇ q5) ◇ q5)) ◇ ((q5 ◇ q5) ◇ q5)))) (apc5 q5)).symm).trans ((h ((q5 ◇ q5) ◇ q5) (((q5 ◇ q5) ◇ q5) ◇ ((q5 ◇ q5) ◇ q5)) q6).symm))
  have apc9 : forall (q7 q8:G), (q7 ◇ ((q7 ◇ q7) ◇ q7)) = (q7 ◇ (q8 ◇ q7)):=by
    intro q7 q8
    exact ((((cg (fun t => q7 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => ((q7 ◇ q7) ◇ q7) ◇ t) (apc5 q7)))).trans (cg (fun t => q7 ◇ t) (cg (fun t => q8 ◇ t) (apc6 q7 (q7 ◇ q7))))).symm).trans ((((cg (fun t => t ◇ (q8 ◇ (((q7 ◇ q7) ◇ q7) ◇ ((((q7 ◇ q7) ◇ q7) ◇ ((q7 ◇ q7) ◇ q7)) ◇ ((q7 ◇ q7) ◇ q7))))) ((h q7 (q7 ◇ q7) (((q7 ◇ q7) ◇ q7) ◇ ((q7 ◇ q7) ◇ q7))).symm)).symm).trans (apc8 ((q7 ◇ q7) ◇ q7) q8)).trans (apc5 q7))).symm
  have apc10 : forall (q9 q10 q11:G), ((q11 ◇ q10) ◇ (q10 ◇ (q9 ◇ q10))) = q10:=by
    intro q9 q10 q11
    exact ((cg (fun t => (q11 ◇ q10) ◇ t) (apc9 q10 q9)).symm).trans ((h q10 q11 q10).symm)
  have apc11 : forall (q12 q13:G), ((q12 ◇ q13) ◇ (((q12 ◇ q13) ◇ (q12 ◇ q13)) ◇ (q12 ◇ q13))) = q13:=by
    intro q12 q13
    exact (((apc10 (q13 ◇ q13) q13 q12).symm).trans (((cg (fun t => (q12 ◇ q13) ◇ t) ((apc9 q13 q12).symm)).symm).trans ((apc9 (q12 ◇ q13) q13).symm))).symm
  have apc12 : forall (q14 q15 q16:G), ((q14 ◇ q15) ◇ (q16 ◇ (q14 ◇ q15))) = q15:=by
    intro q14 q15 q16
    exact (((apc11 q14 q15).symm).trans (apc9 (q14 ◇ q15) q16)).symm
  have apc14 : forall (q17 q18 q19:G), ((q19 ◇ (q17 ◇ q18)) ◇ q18) = (q17 ◇ q18):=by
    intro q17 q18 q19
    exact ((cg (fun t => (q19 ◇ (q17 ◇ q18)) ◇ t) (apc10 q17 q18 q17)).symm).trans (apc10 q18 (q17 ◇ q18) q19)
  have apc15 : forall (q20 q21 q22 q23:G), ((q23 ◇ q21) ◇ (q22 ◇ (q20 ◇ q21))) = q21:=by
    intro q20 q21 q22 q23
    exact (((cg (fun t => t ◇ (q22 ◇ (q20 ◇ q21))) (cg (fun t => q23 ◇ t) (apc12 q20 q21 q22))).symm).trans (apc14 (q20 ◇ q21) (q22 ◇ (q20 ◇ q21)) q23)).trans (apc12 q20 q21 q22)
  have apc16 : forall (q24 q25:G), ((q25 ◇ q25) ◇ q25) = (q24 ◇ q25):=by
    intro q24 q25
    exact (((apc14 q24 q25 q25).symm).trans (((cg (fun t => t ◇ q25) (apc9 q25 q24)).symm).trans (apc14 (q25 ◇ q25) q25 q25))).symm
  have apc17 : forall (q24 q25:G), (q25 ◇ q25) = (q24 ◇ q25):=by
    intro q24 q25
    exact (((apc16 q24 q25).symm).trans (apc16 q25 q25)).symm
  have apc18 : forall (q26 q27 q28:G), ((q28 ◇ (q26 ◇ q27)) ◇ (q28 ◇ (q26 ◇ q27))) = q27:=by
    intro q26 q27 q28
    exact (apc17 (q26 ◇ q27) (q28 ◇ (q26 ◇ q27))).trans (apc15 q26 q27 q28 q26)
  have apc19 : forall (q29 q30 q31:G), ((q29 ◇ (q30 ◇ q31)) ◇ ((q30 ◇ q31) ◇ (q30 ◇ q31))) = q31:=by
    intro q29 q30 q31
    exact ((cg (fun t => t ◇ ((q30 ◇ q31) ◇ (q30 ◇ q31))) (apc17 q29 (q30 ◇ q31))).symm).trans (apc18 q30 q31 (q30 ◇ q31))
  have apc20 : forall (q32 q33 q34:G), (q34 ◇ ((q32 ◇ q33) ◇ (q32 ◇ q33))) = q33:=by
    intro q32 q33 q34
    exact (((apc19 (q32 ◇ q33) q32 q33).symm).trans (apc17 q34 ((q32 ◇ q33) ◇ (q32 ◇ q33)))).symm
  have apc22 : forall (q35 q36 q37:G), (q37 ◇ ((q35 ◇ q36) ◇ (q36 ◇ q36))) = q36:=by
    intro q35 q36 q37
    exact ((cg (fun t => q37 ◇ t) (cg (fun t => t ◇ (q36 ◇ q36)) (apc17 q35 q36))).symm).trans (apc20 q36 q36 q37)
  have apc23 : forall (q38 q39 q40 q41:G), (q41 ◇ ((q39 ◇ q40) ◇ (q38 ◇ q40))) = q40:=by
    intro q38 q39 q40 q41
    exact ((cg (fun t => q41 ◇ t) (cg (fun t => (q39 ◇ q40) ◇ t) (apc17 q38 q40))).symm).trans (apc22 q39 q40 q41)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ z) ◇ ((z ◇ x) ◇ (y ◇ x))):=(apc23 y z x (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18127_to_19390 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18127_to_19390
