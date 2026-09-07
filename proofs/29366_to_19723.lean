-- Equation29366 → Equation19723
-- Recorded verdict: true
-- Premise: x = (x ◇ (y ◇ (y ◇ (z ◇ y)))) ◇ z
-- Conclusion: x = (x ◇ y) ◇ ((y ◇ (z ◇ z)) ◇ z)
-- Original submission SHA-256: 4a748a38206ca3cd1afc9b8ceee185d45c683c37cb5fb56f78780fe2a4e0884f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ (y ◇ (z ◇ y)))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((y ◇ (z ◇ z)) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((x ◇ (y ◇ (y ◇ (z ◇ y)))) ◇ z) = ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (q0 ◇ (q1 ◇ (q1 ◇ ((q2 ◇ (q2 ◇ (q3 ◇ q2))) ◇ q1)))) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ q3) ((h q0 q1 (q2 ◇ (q2 ◇ (q3 ◇ q2)))).symm)).symm).trans ((h (q0 ◇ (q1 ◇ (q1 ◇ ((q2 ◇ (q2 ◇ (q3 ◇ q2))) ◇ q1)))) q2 q3).symm)).symm
  have apc3 : forall (q4 q5 q6:G), ((q6 ◇ q5) ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) = q6:=by
    intro q4 q5 q6
    exact ((cg (fun t => t ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) (apc2 q6 q4 q4 q5)).symm).trans ((h q6 q4 (q4 ◇ (q4 ◇ (q5 ◇ q4)))).symm)
  have apc4 : forall (q7 q8 q9 q10:G), (q7 ◇ (q9 ◇ (q9 ◇ (q10 ◇ q9)))) = (q7 ◇ (q8 ◇ (q8 ◇ (q10 ◇ q8)))):=by
    intro q7 q8 q9 q10
    exact ((cg (fun t => t ◇ (q9 ◇ (q9 ◇ (q10 ◇ q9)))) ((h q7 q8 q10).symm)).symm).trans (apc3 q9 q10 (q7 ◇ (q8 ◇ (q8 ◇ (q10 ◇ q8)))))
  have apc5 : forall (q11 q12:G), (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) = (q12 ◇ (q11 ◇ (q11 ◇ (q12 ◇ q11)))):=by
    intro q11 q12
    exact (((cg (fun t => t ◇ (q11 ◇ (q11 ◇ (q12 ◇ q11)))) (apc1 q12 q11 q11)).symm).trans (apc3 q11 q12 (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))))).symm
  have apc6 : forall (q13 q14:G), ((q14 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13)))) ◇ q14) = q14:=by
    intro q13 q14
    exact ((cg (fun t => t ◇ q14) (apc4 q14 q13 q14 q14)).symm).trans (apc1 q14 q13 q13)
  have apc7 : forall (q7 q8 q9 q10:G), (q7 ◇ (q8 ◇ (q8 ◇ (q10 ◇ q8)))) = (q7 ◇ (q7 ◇ (q7 ◇ (q10 ◇ q7)))):=by
    intro q7 q8 q9 q10
    exact ((apc4 q7 q8 q7 q10).symm).trans (apc4 q7 q7 q7 q10)
  have apc10 : forall (q15 q16 q17:G), (q16 ◇ (q16 ◇ (q16 ◇ ((q17 ◇ (q17 ◇ q15)) ◇ q16)))) = (q16 ◇ (q15 ◇ (q15 ◇ (q15 ◇ (q17 ◇ q15))))):=by
    intro q15 q16 q17
    exact ((apc7 q16 q15 (q16 ◇ (q15 ◇ (q15 ◇ ((q17 ◇ (q17 ◇ q15)) ◇ q15)))) (q17 ◇ (q17 ◇ q15))).symm).trans ((((cg (fun t => q16 ◇ t) (cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => q17 ◇ t) (cg (fun t => q17 ◇ t) ((h q15 q15 q17).symm))))))).symm).trans (apc2 q16 q15 q17 (q15 ◇ (q15 ◇ (q15 ◇ (q17 ◇ q15)))))).trans (cg (fun t => q16 ◇ t) (apc7 q15 q15 (q15 ◇ (q15 ◇ (q15 ◇ (q17 ◇ q15)))) q17)))
  have apc11 : forall (q18 q19:G), (q19 ◇ (q19 ◇ (q19 ◇ (q18 ◇ q19)))) = (q19 ◇ (q18 ◇ (q18 ◇ (q18 ◇ q18)))):=by
    intro q18 q19
    exact ((cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q19) (apc6 q18 q18))))).symm).trans ((((cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q19) (cg (fun t => (q18 ◇ (q18 ◇ (q18 ◇ (q18 ◇ q18)))) ◇ t) (apc6 q18 q18)))))).symm).trans (apc10 q18 q19 (q18 ◇ (q18 ◇ (q18 ◇ (q18 ◇ q18)))))).trans (cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => q18 ◇ t) (apc6 q18 q18))))))
  have apc12 : forall (q0 q20 q2:G), ((q20 ◇ (q2 ◇ (q2 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q0))))) = q20:=by
    intro q0 q20 q2
    exact ((cg (fun t => (q20 ◇ (q2 ◇ (q2 ◇ q0))) ◇ t) (apc7 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q0)))) q2)).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q0))))) (cg (fun t => q20 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q0 q0 q2).symm))))).symm).trans ((h q20 q2 (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q0))))).symm))
  have apc14 : forall (q21 q22:G), ((q22 ◇ ((q21 ◇ (q21 ◇ (q21 ◇ q21))) ◇ q21)) ◇ q21) = q22:=by
    intro q21 q22
    exact ((cg (fun t => t ◇ q21) (cg (fun t => q22 ◇ t) (cg (fun t => (q21 ◇ (q21 ◇ (q21 ◇ q21))) ◇ t) (apc12 q21 q21 q21)))).symm).trans ((h q22 (q21 ◇ (q21 ◇ (q21 ◇ q21))) q21).symm)
  have apc15 : forall (q23 q24:G), ((q24 ◇ q23) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ q23))) ◇ q23)) = q24:=by
    intro q23 q24
    exact ((cg (fun t => (q24 ◇ q23) ◇ t) (cg (fun t => (q23 ◇ (q23 ◇ (q23 ◇ q23))) ◇ t) (apc12 q23 q23 q23))).symm).trans (apc3 (q23 ◇ (q23 ◇ (q23 ◇ q23))) q23 q24)
  have apc16 : forall (q25 q26:G), (q25 ◇ ((q26 ◇ (q26 ◇ (q26 ◇ q26))) ◇ q26)) = (q25 ◇ (q25 ◇ (q25 ◇ (q26 ◇ q25)))):=by
    intro q25 q26
    exact (((apc7 q25 q25 (q25 ◇ (q25 ◇ (q25 ◇ (q26 ◇ q25)))) q26).symm).trans (((cg (fun t => t ◇ (q25 ◇ (q25 ◇ (q26 ◇ q25)))) (apc14 q26 q25)).symm).trans (apc3 q25 q26 (q25 ◇ ((q26 ◇ (q26 ◇ (q26 ◇ q26))) ◇ q26))))).symm
  have apc17 : forall (q27:G), (q27 ◇ (q27 ◇ (q27 ◇ (q27 ◇ (q27 ◇ (q27 ◇ q27)))))) = (q27 ◇ q27):=by
    intro q27
    exact (((cg (fun t => q27 ◇ t) (cg (fun t => q27 ◇ t) (apc16 q27 q27))).symm).trans (apc10 (q27 ◇ q27) q27 q27)).trans (cg (fun t => q27 ◇ t) (apc3 (q27 ◇ q27) q27 q27))
  have apc18 : forall (q28 q29:G), (q29 ◇ (q29 ◇ (q29 ◇ (q28 ◇ (q28 ◇ (q29 ◇ q28)))))) = (q29 ◇ q29):=by
    intro q28 q29
    exact ((cg (fun t => q29 ◇ t) (cg (fun t => q29 ◇ t) (apc5 q28 q29))).symm).trans (apc17 q29)
  have apc19 : forall (q30 q31 q32:G), (q30 ◇ ((q32 ◇ (q31 ◇ q32)) ◇ (q32 ◇ (q32 ◇ (q32 ◇ q32))))) = (q30 ◇ (q31 ◇ (q31 ◇ q32))):=by
    intro q30 q31 q32
    exact ((cg (fun t => q30 ◇ t) (apc11 q32 (q32 ◇ (q31 ◇ q32)))).symm).trans (((cg (fun t => t ◇ ((q32 ◇ (q31 ◇ q32)) ◇ ((q32 ◇ (q31 ◇ q32)) ◇ ((q32 ◇ (q31 ◇ q32)) ◇ (q32 ◇ (q32 ◇ (q31 ◇ q32))))))) (apc12 q32 q30 q31)).symm).trans (apc12 (q32 ◇ (q31 ◇ q32)) (q30 ◇ (q31 ◇ (q31 ◇ q32))) q32))
  have apc20 : forall (q33 q34:G), (q34 ◇ (q33 ◇ (q33 ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33)))))) = (q34 ◇ (q33 ◇ q33)):=by
    intro q33 q34
    exact (((((cg (fun t => q34 ◇ t) (apc7 q33 (q33 ◇ (q33 ◇ (q33 ◇ q33))) (q33 ◇ ((q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ ((q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ ((q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33))))))) (q33 ◇ (q33 ◇ (q33 ◇ q33))))).trans (cg (fun t => q34 ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => q33 ◇ t) (apc16 q33 q33))))).trans (cg (fun t => q34 ◇ t) (apc18 q33 q33))).symm).trans (((cg (fun t => q34 ◇ t) (cg (fun t => t ◇ ((q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ ((q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ ((q33 ◇ (q33 ◇ (q33 ◇ q33))) ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33))))))) (apc12 q33 q33 q33))).symm).trans (apc19 q34 q33 (q33 ◇ (q33 ◇ (q33 ◇ q33)))))).symm
  have apc21 : forall (q35:G), (q35 ◇ (q35 ◇ q35)) = (q35 ◇ q35):=by
    intro q35
    exact ((apc20 q35 q35).symm).trans (apc18 q35 q35)
  have apc22 : forall (q36:G), ((q36 ◇ q36) ◇ q36) = q36:=by
    intro q36
    exact (((cg (fun t => t ◇ q36) (cg (fun t => q36 ◇ t) (apc21 q36))).trans (cg (fun t => t ◇ q36) (apc21 q36))).symm).trans (((cg (fun t => t ◇ q36) (cg (fun t => q36 ◇ t) (cg (fun t => q36 ◇ t) (apc21 q36)))).symm).trans (apc6 q36 q36))
  have apc23 : forall (q37 q38:G), ((q38 ◇ q37) ◇ (q37 ◇ q37)) = q38:=by
    intro q37 q38
    exact ((cg (fun t => (q38 ◇ q37) ◇ t) (apc21 q37)).symm).trans (((cg (fun t => (q38 ◇ q37) ◇ t) (cg (fun t => q37 ◇ t) (apc21 q37))).symm).trans (apc3 q37 q37 q38))
  have apc25 : forall (q23 q24 q35:G), ((q24 ◇ q23) ◇ q23) = q24:=by
    intro q23 q24 q35
    exact ((cg (fun t => (q24 ◇ q23) ◇ t) (apc22 q23)).symm).trans ((((cg (fun t => (q24 ◇ q23) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc21 q23)))).trans (cg (fun t => (q24 ◇ q23) ◇ t) (cg (fun t => t ◇ q23) (apc21 q23)))).symm).trans (apc15 q23 q24))
  have apc26 : forall (q39 q40:G), (q39 ◇ (q40 ◇ q40)) = (q39 ◇ q40):=by
    intro q39 q40
    exact ((cg (fun t => t ◇ (q40 ◇ q40)) (apc25 q40 q39 q39)).symm).trans (apc23 q40 (q39 ◇ q40))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ ((y ◇ (z ◇ z)) ◇ z)):=(((cg (fun t => (x ◇ y) ◇ t) (cg (fun t => t ◇ z) (apc26 y z))).trans (cg (fun t => (x ◇ y) ◇ t) (apc25 z y ((y ◇ z) ◇ z)))).trans (apc25 y x ((x ◇ y) ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29366_to_19723 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29366_to_19723
