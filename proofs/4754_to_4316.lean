-- Equation4754 → Equation4316
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ y))))
-- Conclusion: x ◇ (y ◇ x) = x ◇ (z ◇ x)
-- Original submission SHA-256: cef206092866977f839657b56caa10b64777e1aaccdaf1f84c97246716c40a84
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = x ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (q1 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) ((h q1 q1 q0).symm))).symm).trans ((h q1 (q1 ◇ (q0 ◇ q1)) q1).symm)
  have apc1 : forall (q2:G), (q2 ◇ (q2 ◇ q2)) = q2:=by
    intro q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q2) (apc0 q2 q2))).symm).trans (apc0 (q2 ◇ (q2 ◇ q2)) q2)
  have apc2 : forall (q3:G), (q3 ◇ q3) = q3:=by
    intro q3
    exact ((cg (fun t => q3 ◇ t) (apc1 q3)).symm).trans (((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (apc1 q3)))).symm).trans ((h q3 q3 q3).symm))
  have apc3 : forall (q3 q4:G), ((q4 ◇ q3) ◇ (q3 ◇ (q4 ◇ q3))) = (q4 ◇ q3):=by
    intro q3 q4
    exact ((cg (fun t => (q4 ◇ q3) ◇ t) (cg (fun t => q3 ◇ t) (apc1 (q4 ◇ q3)))).symm).trans ((h (q4 ◇ q3) q3 q4).symm)
  have apc4 : forall (q5 q6:G), (q5 ◇ (q6 ◇ (q5 ◇ (q5 ◇ q6)))) = q5:=by
    intro q5 q6
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => q5 ◇ t) (apc2 q6))))).symm).trans ((h q5 q6 q6).symm)
  have apc6 : forall (q7 q8:G), ((q8 ◇ (q7 ◇ q8)) ◇ (q7 ◇ q8)) = (q8 ◇ (q7 ◇ q8)):=by
    intro q7 q8
    exact ((cg (fun t => (q8 ◇ (q7 ◇ q8)) ◇ t) (apc3 q8 q7)).symm).trans (apc3 (q7 ◇ q8) q8)
  have apc13 : forall (q9 q10:G), ((q9 ◇ (q10 ◇ q9)) ◇ (q9 ◇ (q9 ◇ (q10 ◇ q9)))) = (q9 ◇ (q10 ◇ q9)):=by
    intro q9 q10
    exact ((cg (fun t => (q9 ◇ (q10 ◇ q9)) ◇ t) (cg (fun t => q9 ◇ t) (apc2 (q9 ◇ (q10 ◇ q9))))).symm).trans (((cg (fun t => (q9 ◇ (q10 ◇ q9)) ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => (q9 ◇ (q10 ◇ q9)) ◇ t) (apc6 q10 q9)))).symm).trans ((h (q9 ◇ (q10 ◇ q9)) q9 q10).symm))
  have apc16 : forall (q11 q12 q13:G), (q13 ◇ ((q11 ◇ (q12 ◇ q11)) ◇ (q13 ◇ (q13 ◇ (q12 ◇ q11))))) = q13:=by
    intro q11 q12 q13
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => (q11 ◇ (q12 ◇ q11)) ◇ t) (cg (fun t => q13 ◇ t) (cg (fun t => q13 ◇ t) (apc3 q11 q12))))).symm).trans ((h q13 (q11 ◇ (q12 ◇ q11)) (q12 ◇ q11)).symm)
  have apc17 : forall (q14 q15:G), (q15 ◇ (q15 ◇ (q14 ◇ q15))) = q15:=by
    intro q14 q15
    exact ((cg (fun t => q15 ◇ t) (apc13 q15 q14)).symm).trans (apc16 q15 q14 q15)
  have apc18 : forall (q16 q17:G), (q17 ◇ ((q16 ◇ q17) ◇ q17)) = q17:=by
    intro q16 q17
    exact ((cg (fun t => q17 ◇ t) (cg (fun t => (q16 ◇ q17) ◇ t) (apc2 q17))).symm).trans (((cg (fun t => q17 ◇ t) (cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => q17 ◇ t) (apc17 q16 q17)))).symm).trans ((h q17 (q16 ◇ q17) q17).symm))
  have apc21 : forall (q18 q19:G), ((q18 ◇ (q19 ◇ (q19 ◇ q18))) ◇ q19) = (q18 ◇ (q19 ◇ (q19 ◇ q18))):=by
    intro q18 q19
    exact ((cg (fun t => (q18 ◇ (q19 ◇ (q19 ◇ q18))) ◇ t) (apc4 q19 q18)).symm).trans (((cg (fun t => (q18 ◇ (q19 ◇ (q19 ◇ q18))) ◇ t) (cg (fun t => t ◇ (q18 ◇ (q19 ◇ (q19 ◇ q18)))) (apc4 q19 q18))).symm).trans (apc18 q19 (q18 ◇ (q19 ◇ (q19 ◇ q18)))))
  have apc22 : forall (q16 q20 q17:G), (q20 ◇ ((q17 ◇ (q16 ◇ q17)) ◇ (q20 ◇ (q20 ◇ q17)))) = q20:=by
    intro q16 q20 q17
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => (q17 ◇ (q16 ◇ q17)) ◇ t) (cg (fun t => q20 ◇ t) (cg (fun t => q20 ◇ t) (apc17 q16 q17))))).symm).trans ((h q20 (q17 ◇ (q16 ◇ q17)) q17).symm)
  have apc24 : forall (q21 q22 q23:G), (q22 ◇ (((q21 ◇ q23) ◇ q23) ◇ (q22 ◇ (q22 ◇ q23)))) = q22:=by
    intro q21 q22 q23
    exact ((cg (fun t => q22 ◇ t) (cg (fun t => ((q21 ◇ q23) ◇ q23) ◇ t) (cg (fun t => q22 ◇ t) (cg (fun t => q22 ◇ t) (apc18 q21 q23))))).symm).trans ((h q22 ((q21 ◇ q23) ◇ q23) q23).symm)
  have apc25 : forall (q24 q25 q26:G), (q26 ◇ (((q24 ◇ q26) ◇ (q25 ◇ (q24 ◇ q26))) ◇ q26)) = q26:=by
    intro q24 q25 q26
    exact ((cg (fun t => q26 ◇ t) (cg (fun t => ((q24 ◇ q26) ◇ (q25 ◇ (q24 ◇ q26))) ◇ t) (apc17 q24 q26))).symm).trans (apc22 q25 q26 (q24 ◇ q26))
  have apc45 : forall (q27 q28 q29:G), (q28 ◇ (q29 ◇ (q28 ◇ (q28 ◇ (q27 ◇ (q29 ◇ (q29 ◇ q27))))))) = q28:=by
    intro q27 q28 q29
    exact ((cg (fun t => q28 ◇ t) (cg (fun t => q29 ◇ t) (cg (fun t => q28 ◇ t) (cg (fun t => q28 ◇ t) (apc21 q27 q29))))).symm).trans ((h q28 q29 (q27 ◇ (q29 ◇ (q29 ◇ q27)))).symm)
  have apc61 : forall (q30 q31 q32:G), (q32 ◇ (((q31 ◇ (q32 ◇ (q30 ◇ q32))) ◇ (q32 ◇ (q30 ◇ q32))) ◇ q32)) = q32:=by
    intro q30 q31 q32
    exact ((cg (fun t => q32 ◇ t) (cg (fun t => ((q31 ◇ (q32 ◇ (q30 ◇ q32))) ◇ (q32 ◇ (q30 ◇ q32))) ◇ t) (apc2 q32))).symm).trans (((cg (fun t => q32 ◇ t) (cg (fun t => ((q31 ◇ (q32 ◇ (q30 ◇ q32))) ◇ (q32 ◇ (q30 ◇ q32))) ◇ t) (cg (fun t => q32 ◇ t) (apc17 q30 q32)))).symm).trans (apc24 q31 q32 (q32 ◇ (q30 ◇ q32))))
  have apc62 : forall (q33 q34:G), (((q33 ◇ q34) ◇ q34) ◇ ((q33 ◇ q34) ◇ ((q33 ◇ q34) ◇ q34))) = ((q33 ◇ q34) ◇ q34):=by
    intro q33 q34
    exact ((cg (fun t => ((q33 ◇ q34) ◇ q34) ◇ t) (cg (fun t => t ◇ ((q33 ◇ q34) ◇ q34)) (apc24 q33 (q33 ◇ q34) q34))).symm).trans (((cg (fun t => ((q33 ◇ q34) ◇ q34) ◇ t) (cg (fun t => t ◇ ((q33 ◇ q34) ◇ q34)) (cg (fun t => t ◇ (((q33 ◇ q34) ◇ q34) ◇ ((q33 ◇ q34) ◇ ((q33 ◇ q34) ◇ q34)))) (apc24 q33 (q33 ◇ q34) q34)))).symm).trans (apc61 (q33 ◇ q34) (q33 ◇ q34) ((q33 ◇ q34) ◇ q34)))
  have apc63 : forall (q35 q36:G), ((q35 ◇ q36) ◇ ((q35 ◇ q36) ◇ q36)) = (q35 ◇ q36):=by
    intro q35 q36
    exact ((cg (fun t => (q35 ◇ q36) ◇ t) (apc62 q35 q36)).symm).trans (apc24 q35 (q35 ◇ q36) q36)
  have apc66 : forall (q37 q38 q39:G), ((q37 ◇ (q39 ◇ q38)) ◇ (q38 ◇ (q37 ◇ (q39 ◇ q38)))) = (q37 ◇ (q39 ◇ q38)):=by
    intro q37 q38 q39
    exact ((cg (fun t => (q37 ◇ (q39 ◇ q38)) ◇ t) (cg (fun t => q38 ◇ t) (apc63 q37 (q39 ◇ q38)))).symm).trans ((h (q37 ◇ (q39 ◇ q38)) q38 q39).symm)
  have apc75 : forall (q40 q41 q42:G), ((q41 ◇ (q40 ◇ (q42 ◇ q41))) ◇ (q40 ◇ (q42 ◇ q41))) = (q41 ◇ (q40 ◇ (q42 ◇ q41))):=by
    intro q40 q41 q42
    exact ((cg (fun t => (q41 ◇ (q40 ◇ (q42 ◇ q41))) ◇ t) (apc66 q40 q41 q42)).symm).trans (((cg (fun t => (q41 ◇ (q40 ◇ (q42 ◇ q41))) ◇ t) (cg (fun t => t ◇ (q41 ◇ (q40 ◇ (q42 ◇ q41)))) (apc66 q40 q41 q42))).symm).trans (apc18 (q40 ◇ (q42 ◇ q41)) (q41 ◇ (q40 ◇ (q42 ◇ q41)))))
  have apc109 : forall (q43 q44 q45 q46:G), (q45 ◇ ((((q43 ◇ q46) ◇ (q44 ◇ (q43 ◇ q46))) ◇ q46) ◇ (q45 ◇ (q45 ◇ q46)))) = q45:=by
    intro q43 q44 q45 q46
    exact ((cg (fun t => q45 ◇ t) (cg (fun t => (((q43 ◇ q46) ◇ (q44 ◇ (q43 ◇ q46))) ◇ q46) ◇ t) (cg (fun t => q45 ◇ t) (cg (fun t => q45 ◇ t) (apc25 q43 q44 q46))))).symm).trans ((h q45 (((q43 ◇ q46) ◇ (q44 ◇ (q43 ◇ q46))) ◇ q46) q46).symm)
  have apc129 : forall (q47 q48 q49:G), (q49 ◇ ((q47 ◇ (q48 ◇ (q48 ◇ q47))) ◇ (q49 ◇ (q49 ◇ (q48 ◇ (q48 ◇ q47)))))) = q49:=by
    intro q47 q48 q49
    exact (((cg (fun t => q49 ◇ t) (cg (fun t => t ◇ (q49 ◇ (q49 ◇ (q48 ◇ (q48 ◇ q47))))) (cg (fun t => t ◇ (q48 ◇ (q48 ◇ q47))) (apc21 q47 q48)))).trans (cg (fun t => q49 ◇ t) (cg (fun t => t ◇ (q49 ◇ (q49 ◇ (q48 ◇ (q48 ◇ q47))))) (apc75 q48 q47 q48)))).symm).trans (((cg (fun t => q49 ◇ t) (cg (fun t => t ◇ (q49 ◇ (q49 ◇ (q48 ◇ (q48 ◇ q47))))) (cg (fun t => t ◇ (q48 ◇ (q48 ◇ q47))) (cg (fun t => (q47 ◇ (q48 ◇ (q48 ◇ q47))) ◇ t) (apc4 q48 q47))))).symm).trans (apc109 q47 q48 q49 (q48 ◇ (q48 ◇ q47))))
  have apc139 : forall (q50 q51:G), ((q50 ◇ (q51 ◇ (q51 ◇ q50))) ◇ (q50 ◇ (q50 ◇ (q51 ◇ (q51 ◇ q50))))) = (q50 ◇ (q51 ◇ (q51 ◇ q50))):=by
    intro q50 q51
    exact ((cg (fun t => (q50 ◇ (q51 ◇ (q51 ◇ q50))) ◇ t) (cg (fun t => t ◇ (q50 ◇ (q51 ◇ (q51 ◇ q50)))) (apc129 q50 q51 q50))).symm).trans (((cg (fun t => (q50 ◇ (q51 ◇ (q51 ◇ q50))) ◇ t) (cg (fun t => t ◇ (q50 ◇ (q51 ◇ (q51 ◇ q50)))) (cg (fun t => t ◇ ((q50 ◇ (q51 ◇ (q51 ◇ q50))) ◇ (q50 ◇ (q50 ◇ (q51 ◇ (q51 ◇ q50)))))) (apc129 q50 q51 q50)))).symm).trans (apc61 q50 q50 (q50 ◇ (q51 ◇ (q51 ◇ q50)))))
  have apc140 : forall (q52 q53:G), (q53 ◇ (q53 ◇ (q52 ◇ (q52 ◇ q53)))) = q53:=by
    intro q52 q53
    exact ((cg (fun t => q53 ◇ t) (apc139 q53 q52)).symm).trans (apc129 q53 q52 q53)
  have apc141 : forall (q54 q55:G), (q54 ◇ (q55 ◇ q54)) = q54:=by
    intro q54 q55
    exact ((cg (fun t => q54 ◇ t) (cg (fun t => q55 ◇ t) (apc2 q54))).symm).trans (((cg (fun t => q54 ◇ t) (cg (fun t => q55 ◇ t) (cg (fun t => q54 ◇ t) (apc140 q55 q54)))).symm).trans (apc45 q54 q54 q55))
  exact (calc
    (x ◇ (y ◇ x)) = x:=apc141 x y
    _ = (x ◇ (z ◇ x)):=(apc141 x z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4754_to_4316 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4754_to_4316
