-- Equation23412 → Equation29670
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ z) ◇ (y ◇ (y ◇ z))
-- Conclusion: x = (y ◇ (y ◇ (y ◇ (z ◇ z)))) ◇ x
-- Original submission SHA-256: 30d5dfc75fff505484504d90fb236f36a66c7d2f8d157745e5d26a1ba7b99741
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ z) ◇ (y ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ (y ◇ (z ◇ z)))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (((y ◇ x) ◇ z) ◇ (y ◇ (y ◇ z))) = (((x ◇ x) ◇ x) ◇ (x ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (((x ◇ x) ◇ x) ◇ (x ◇ (x ◇ x))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q2))))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q2))))) ((h q0 q1 q2).symm)).symm).trans ((h q2 (q1 ◇ q0) (q1 ◇ (q1 ◇ q2))).symm)
  have apc3 : forall (q3 q4 q5 q6:G), ((q3 ◇ q5) ◇ ((q3 ◇ q5) ◇ (q3 ◇ (q3 ◇ q4)))) = ((q4 ◇ q6) ◇ (q5 ◇ (q5 ◇ q6))):=by
    intro q3 q4 q5 q6
    exact (((cg (fun t => t ◇ (q5 ◇ (q5 ◇ q6))) (cg (fun t => t ◇ q6) (apc2 q5 q3 q4))).symm).trans ((h ((q3 ◇ q5) ◇ ((q3 ◇ q5) ◇ (q3 ◇ (q3 ◇ q4)))) q5 q6).symm)).symm
  have apc4 : forall (q7 q8 q9:G), (q8 ◇ ((q9 ◇ q7) ◇ (q8 ◇ (q8 ◇ q7)))) = q9:=by
    intro q7 q8 q9
    exact ((cg (fun t => q8 ◇ t) (apc3 q7 q9 q8 q7)).symm).trans (apc2 q8 q7 q9)
  have apc5 : forall (q3 q4 q5 q6:G), ((q4 ◇ q6) ◇ (q5 ◇ (q5 ◇ q6))) = ((q4 ◇ q3) ◇ (q5 ◇ (q5 ◇ q3))):=by
    intro q3 q4 q5 q6
    exact ((apc3 q3 q4 q5 q6).symm).trans (apc3 q3 q4 q5 q3)
  have apc6 : forall (q10 q11:G), (((q11 ◇ q11) ◇ q10) ◇ (q11 ◇ (q11 ◇ q10))) = q11:=by
    intro q10 q11
    exact ((apc5 q10 (q11 ◇ q11) q11 q11).symm).trans (apc1 q11 q10 q10)
  have apc7 : forall (q12 q13 q14:G), ((q12 ◇ (q14 ◇ (q12 ◇ (q12 ◇ q13)))) ◇ q13) = q14:=by
    intro q12 q13 q14
    exact ((cg (fun t => (q12 ◇ (q14 ◇ (q12 ◇ (q12 ◇ q13)))) ◇ t) (apc2 (q14 ◇ (q12 ◇ (q12 ◇ q13))) q12 q13)).symm).trans (apc4 (q12 ◇ (q12 ◇ q13)) (q12 ◇ (q14 ◇ (q12 ◇ (q12 ◇ q13)))) q14)
  have apc10 : forall (q15 q16:G), (((q16 ◇ q15) ◇ q16) ◇ ((q16 ◇ q15) ◇ q15)) = (q16 ◇ q15):=by
    intro q15 q16
    exact ((cg (fun t => t ◇ ((q16 ◇ q15) ◇ q15)) (cg (fun t => (q16 ◇ q15) ◇ t) (apc4 q15 (q16 ◇ q15) q16))).symm).trans (apc7 (q16 ◇ q15) ((q16 ◇ q15) ◇ q15) (q16 ◇ q15))
  have apc12 : forall (q17 q18 q19 q20:G), (q20 ◇ (q17 ◇ (q20 ◇ (q20 ◇ (q18 ◇ (q18 ◇ q19)))))) = ((q18 ◇ q17) ◇ q19):=by
    intro q17 q18 q19 q20
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => t ◇ (q20 ◇ (q20 ◇ (q18 ◇ (q18 ◇ q19))))) ((h q17 q18 q19).symm))).symm).trans (apc4 (q18 ◇ (q18 ◇ q19)) q20 ((q18 ◇ q17) ◇ q19))
  have apc13 : forall (q21 q22 q23:G), (((q21 ◇ q23) ◇ q22) ◇ q23) = ((q21 ◇ q23) ◇ (q22 ◇ q21)):=by
    intro q21 q22 q23
    exact (((cg (fun t => (q21 ◇ q23) ◇ t) (cg (fun t => q22 ◇ t) (apc4 q23 (q21 ◇ q23) q21))).symm).trans (apc12 q22 (q21 ◇ q23) q23 (q21 ◇ q23))).symm
  have apc14 : forall (q24 q25:G), ((q25 ◇ q25) ◇ (q25 ◇ q24)) = (q25 ◇ ((q25 ◇ q25) ◇ q24)):=by
    intro q24 q25
    exact (((cg (fun t => q25 ◇ t) (apc12 q25 q25 q24 q25)).symm).trans (apc12 q25 q25 (q25 ◇ q24) q25)).symm
  have apc15 : forall (q26:G), (q26 ◇ (q26 ◇ ((q26 ◇ q26) ◇ (q26 ◇ q26)))) = q26:=by
    intro q26
    exact ((cg (fun t => q26 ◇ t) (apc14 (q26 ◇ q26) q26)).symm).trans (apc4 q26 q26 q26)
  have apc16 : forall (q27:G), ((q27 ◇ q27) ◇ q27) = q27:=by
    intro q27
    exact (((cg (fun t => (q27 ◇ q27) ◇ t) (cg (fun t => t ◇ (q27 ◇ ((q27 ◇ q27) ◇ (q27 ◇ q27)))) (apc15 q27))).trans (cg (fun t => (q27 ◇ q27) ◇ t) (apc15 q27))).symm).trans ((((cg (fun t => t ◇ ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ (q27 ◇ q27)))) ◇ (q27 ◇ ((q27 ◇ q27) ◇ (q27 ◇ q27))))) (cg (fun t => t ◇ q27) (apc15 q27))).symm).trans (apc10 (q27 ◇ ((q27 ◇ q27) ◇ (q27 ◇ q27))) q27)).trans (apc15 q27))
  have apc17 : forall (q28:G), (q28 ◇ (q28 ◇ (q28 ◇ q28))) = q28:=by
    intro q28
    exact ((cg (fun t => t ◇ (q28 ◇ (q28 ◇ q28))) (apc16 q28)).symm).trans ((h q28 q28 q28).symm)
  have apc18 : forall (q29:G), ((q29 ◇ q29) ◇ (q29 ◇ q29)) = (q29 ◇ q29):=by
    intro q29
    exact (((cg (fun t => t ◇ q29) (apc16 q29)).symm).trans (apc13 q29 q29 q29)).symm
  have apc21 : forall (q30 q31:G), ((q30 ◇ q30) ◇ ((q31 ◇ q30) ◇ q30)) = q31:=by
    intro q30 q31
    exact ((cg (fun t => (q30 ◇ q30) ◇ t) (cg (fun t => (q31 ◇ q30) ◇ t) (apc16 q30))).symm).trans (((cg (fun t => (q30 ◇ q30) ◇ t) (cg (fun t => (q31 ◇ q30) ◇ t) (cg (fun t => (q30 ◇ q30) ◇ t) (apc16 q30)))).symm).trans (apc4 q30 (q30 ◇ q30) q31))
  have apc22 : forall (q32 q33:G), (q33 ◇ ((q32 ◇ q32) ◇ q33)) = (q32 ◇ q32):=by
    intro q32 q33
    exact (((cg (fun t => t ◇ ((q32 ◇ q32) ◇ q33)) (cg (fun t => t ◇ ((q33 ◇ q32) ◇ q32)) (apc18 q32))).trans (cg (fun t => t ◇ ((q32 ◇ q32) ◇ q33)) (apc21 q32 q33))).symm).trans (((cg (fun t => (((q32 ◇ q32) ◇ (q32 ◇ q32)) ◇ ((q33 ◇ q32) ◇ q32)) ◇ t) (cg (fun t => (q32 ◇ q32) ◇ t) (apc21 q32 q33))).symm).trans (apc6 ((q33 ◇ q32) ◇ q32) (q32 ◇ q32)))
  have apc28 : forall (q34 q35:G), ((q34 ◇ (q35 ◇ q34)) ◇ (q34 ◇ q34)) = q35:=by
    intro q34 q35
    exact ((cg (fun t => t ◇ (q34 ◇ q34)) (cg (fun t => q34 ◇ t) (cg (fun t => q35 ◇ t) (apc17 q34)))).symm).trans (apc7 q34 (q34 ◇ q34) q35)
  have apc29 : forall (q36 q37:G), ((q36 ◇ q36) ◇ (q37 ◇ q37)) = (q36 ◇ q36):=by
    intro q36 q37
    exact ((cg (fun t => t ◇ (q37 ◇ q37)) (apc22 q36 q37)).symm).trans (apc28 q37 (q36 ◇ q36))
  have apc30 : forall (q38 q39:G), (q39 ◇ q39) = (q38 ◇ q38):=by
    intro q38 q39
    exact (((apc22 q38 ((q38 ◇ q38) ◇ q38)).symm).trans (((cg (fun t => t ◇ ((q38 ◇ q38) ◇ ((q38 ◇ q38) ◇ q38))) (cg (fun t => t ◇ q38) (apc29 q38 q39))).symm).trans ((h (q39 ◇ q39) (q38 ◇ q38) q38).symm))).symm
  have apc31 : forall (q40 q41:G), ((q40 ◇ q40) ◇ q41) = q41:=by
    intro q40 q41
    exact ((cg (fun t => t ◇ q41) (apc30 q40 q41)).symm).trans (apc16 q41)
  have apc34 : forall (q42 q43:G), (q43 ◇ (q43 ◇ (q42 ◇ q42))) = q43:=by
    intro q42 q43
    exact ((cg (fun t => q43 ◇ t) (cg (fun t => q43 ◇ t) (apc30 q42 q43))).symm).trans (apc17 q43)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (y ◇ (y ◇ (z ◇ z)))) ◇ x):=((cg (fun t => t ◇ x) (cg (fun t => y ◇ t) (apc34 z y))).trans (apc31 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23412_to_29670 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23412_to_29670
