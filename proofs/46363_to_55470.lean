-- Equation46363 → Equation55470
-- Recorded verdict: true
-- Premise: x * y = (y * z) * (y * (y * x))
-- Conclusion: x * (y * z) = w * ((y * u) * u)
-- Original submission SHA-256: 15d49d7ae4265305175b6c7a96e7eda84007989e90f4b1c04f33ca0f54875fd2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ z) ◇ (y ◇ (y ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = w ◇ ((y ◇ u) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ q3))) = (q3 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q1 ◇ q2) ◇ ((q1 ◇ q2) ◇ q3))) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) (q1 ◇ (q1 ◇ q0))).symm)
  have apc1 : forall (q4 q5 q6 q7 q8:G), ((q7 ◇ (q5 ◇ q6)) ◇ ((q4 ◇ q5) ◇ ((q4 ◇ q5) ◇ q8))) = (q8 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7 q8
    exact ((cg (fun t => t ◇ ((q4 ◇ q5) ◇ ((q4 ◇ q5) ◇ q8))) (apc0 q4 q5 q6 q7)).symm).trans ((h q8 (q4 ◇ q5) ((q5 ◇ q6) ◇ ((q5 ◇ q6) ◇ q7))).symm)
  have apc2 : forall (q9 q10 q11 q12:G), ((q9 ◇ q11) ◇ ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ q12))) = (q12 ◇ (q10 ◇ q11)):=by
    intro q9 q10 q11 q12
    exact ((cg (fun t => t ◇ ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ q12))) ((h q9 q11 q9).symm)).symm).trans (apc1 q10 q11 (q11 ◇ q9) (q11 ◇ q9) q12)
  have apc4 : forall (q13 q14 q15 q16:G), ((q14 ◇ q15) ◇ ((q15 ◇ q16) ◇ (q13 ◇ q15))) = ((q15 ◇ (q15 ◇ q13)) ◇ (q15 ◇ q16)):=by
    intro q13 q14 q15 q16
    exact ((cg (fun t => (q14 ◇ q15) ◇ t) (cg (fun t => (q15 ◇ q16) ◇ t) ((h q13 q15 q16).symm))).symm).trans (apc0 q14 q15 q16 (q15 ◇ (q15 ◇ q13)))
  have apc7 : forall (q17 q18:G), ((q18 ◇ (q18 ◇ (q18 ◇ q17))) ◇ (q18 ◇ q17)) = (q18 ◇ (q18 ◇ q17)):=by
    intro q17 q18
    exact ((apc4 (q18 ◇ q17) q17 q18 q17).symm).trans (apc0 q17 q18 q17 q18)
  have apc8 : forall (q19 q20:G), (q20 ◇ (q20 ◇ (q20 ◇ q19))) = (q19 ◇ q20):=by
    intro q19 q20
    exact ((apc7 (q20 ◇ q19) q20).symm).trans ((h q19 q20 (q20 ◇ (q20 ◇ (q20 ◇ q19)))).symm)
  have apc9 : forall (q17 q18 q19 q20:G), ((q17 ◇ q18) ◇ (q18 ◇ q17)) = (q18 ◇ (q18 ◇ q17)):=by
    intro q17 q18 q19 q20
    exact ((cg (fun t => t ◇ (q18 ◇ q17)) (apc8 q17 q18)).symm).trans (apc7 q17 q18)
  have apc10 : forall (q0 q1 q2 q21:G), (((q1 ◇ q2) ◇ q21) ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))) = ((q1 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q21
    exact ((cg (fun t => ((q1 ◇ q2) ◇ q21) ◇ t) (cg (fun t => (q1 ◇ q2) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (q1 ◇ q0)) (q1 ◇ q2) q21).symm)
  have apc11 : forall (q22 q23:G), (q23 ◇ (q22 ◇ q23)) = ((q23 ◇ q22) ◇ q23):=by
    intro q22 q23
    exact ((cg (fun t => q23 ◇ t) (apc8 q22 q23)).symm).trans (apc8 (q23 ◇ q22) q23)
  have apc12 : forall (q24 q25:G), ((q24 ◇ q25) ◇ ((q24 ◇ q24) ◇ q24)) = (q24 ◇ q24):=by
    intro q24 q25
    exact ((cg (fun t => (q24 ◇ q25) ◇ t) (apc11 q24 q24)).symm).trans ((h q24 q24 q25).symm)
  have apc13 : forall (q26 q27:G), ((q26 ◇ q27) ◇ ((q27 ◇ q27) ◇ q27)) = (q27 ◇ q27):=by
    intro q26 q27
    exact ((cg (fun t => t ◇ ((q27 ◇ q27) ◇ q27)) (apc8 q26 q27)).symm).trans (apc12 q27 (q27 ◇ (q27 ◇ q26)))
  have apc15 : forall (q28:G), (((q28 ◇ q28) ◇ q28) ◇ (q28 ◇ q28)) = (q28 ◇ q28):=by
    intro q28
    exact ((cg (fun t => t ◇ (q28 ◇ q28)) (apc11 q28 q28)).symm).trans ((((apc10 q28 q28 q28 (q28 ◇ q28)).symm).trans (apc9 (q28 ◇ q28) (q28 ◇ q28) q28 q28)).trans (((cg (fun t => (q28 ◇ q28) ◇ t) (apc9 q28 q28 ((q28 ◇ q28) ◇ (q28 ◇ q28)) ((q28 ◇ q28) ◇ (q28 ◇ q28)))).trans (cg (fun t => (q28 ◇ q28) ◇ t) (apc11 q28 q28))).trans (apc12 q28 q28)))
  have apc16 : forall (q29 q30:G), ((q29 ◇ q30) ◇ (q30 ◇ q30)) = (q30 ◇ q30):=by
    intro q29 q30
    exact ((cg (fun t => (q29 ◇ q30) ◇ t) (apc15 q30)).symm).trans ((((cg (fun t => (q29 ◇ q30) ◇ t) (cg (fun t => ((q30 ◇ q30) ◇ q30) ◇ t) (apc15 q30))).symm).trans (apc2 q29 (q30 ◇ q30) q30 (q30 ◇ q30))).trans (apc12 q30 q30))
  have apc17 : forall (q31 q32:G), ((q32 ◇ q32) ◇ (q31 ◇ q32)) = (q32 ◇ q32):=by
    intro q31 q32
    exact ((((cg (fun t => (q31 ◇ q32) ◇ t) (apc16 q31 q32)).trans (apc16 q31 q32)).symm).trans (((cg (fun t => (q31 ◇ q32) ◇ t) (cg (fun t => (q31 ◇ q32) ◇ t) (apc16 q31 q32))).symm).trans (apc8 (q32 ◇ q32) (q31 ◇ q32)))).symm
  have apc19 : forall (q33 q34 q35 q36:G), ((q35 ◇ (q33 ◇ q34)) ◇ ((q33 ◇ q33) ◇ q33)) = (q33 ◇ q33):=by
    intro q33 q34 q35 q36
    exact (((cg (fun t => (q35 ◇ (q33 ◇ q34)) ◇ t) (apc9 q33 q33 ((q33 ◇ q33) ◇ (q33 ◇ q33)) ((q33 ◇ q33) ◇ (q33 ◇ q33)))).trans (cg (fun t => (q35 ◇ (q33 ◇ q34)) ◇ t) (apc11 q33 q33))).symm).trans ((((cg (fun t => (q35 ◇ (q33 ◇ q34)) ◇ t) (cg (fun t => (q33 ◇ q33) ◇ t) (apc17 q36 q33))).symm).trans (apc1 q33 q33 q34 q35 (q36 ◇ q33))).trans (apc16 q36 q33))
  have apc20 : forall (q37 q38:G), ((q38 ◇ q38) ◇ ((q37 ◇ q37) ◇ q37)) = (q37 ◇ q37):=by
    intro q37 q38
    exact ((cg (fun t => t ◇ ((q37 ◇ q37) ◇ q37)) (apc17 q37 q38)).symm).trans (apc19 q37 q38 (q38 ◇ q38) q37)
  have apc21 : forall (q39 q40 q41:G), ((q39 ◇ q40) ◇ ((q41 ◇ q41) ◇ q41)) = (q41 ◇ q41):=by
    intro q39 q40 q41
    exact ((cg (fun t => t ◇ ((q41 ◇ q41) ◇ q41)) ((h q39 q40 (q40 ◇ q39)).symm)).symm).trans (apc20 q41 (q40 ◇ (q40 ◇ q39)))
  have apc22 : forall (q42 q43:G), ((q43 ◇ q43) ◇ (q42 ◇ q42)) = (q42 ◇ q42):=by
    intro q42 q43
    exact ((cg (fun t => (q43 ◇ q43) ◇ t) (apc17 (q42 ◇ q42) q42)).symm).trans ((((cg (fun t => (q43 ◇ q43) ◇ t) (cg (fun t => t ◇ ((q42 ◇ q42) ◇ q42)) (apc13 (q42 ◇ q42) q42))).symm).trans (apc20 ((q42 ◇ q42) ◇ q42) q43)).trans (apc21 (q42 ◇ q42) q42 q42))
  have apc23 : forall (q44 q45:G), (q45 ◇ q45) = (q44 ◇ q44):=by
    intro q44 q45
    exact ((((cg (fun t => (q45 ◇ q45) ◇ t) (apc22 q44 q45)).trans (apc22 q44 q45)).symm).trans ((((cg (fun t => (q45 ◇ q45) ◇ t) (cg (fun t => (q45 ◇ q45) ◇ t) (apc22 q44 q45))).symm).trans (apc8 (q44 ◇ q44) (q45 ◇ q45))).trans (apc22 q45 q44))).symm
  have apc24 : forall (q46 q47 q48:G), (q47 ◇ q48) = (q46 ◇ q46):=by
    intro q46 q47 q48
    exact (((apc23 q46 (q48 ◇ (q48 ◇ q47))).symm).trans ((h q47 q48 (q48 ◇ q47)).symm)).symm
  exact (apc24 (x ◇ (y ◇ z)) x (y ◇ z)).trans ((apc24 (x ◇ (y ◇ z)) w ((y ◇ u) ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46363_to_55470 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46363_to_55470
