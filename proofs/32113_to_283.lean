-- Equation32113 → Equation283
-- Recorded verdict: true
-- Premise: x = (y ◇ ((x ◇ (x ◇ z)) ◇ z)) ◇ x
-- Conclusion: x = ((y ◇ y) ◇ y) ◇ x
-- Original submission SHA-256: d8159b2442f33d11d8eff25ead3a9a733585a1bb41bfb50187552c07f4ed95e6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ (x ◇ z)) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ y) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q1)) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) ((h ((q0 ◇ (q0 ◇ q1)) ◇ q1) q0 q0).symm)).symm).trans ((h q0 (q0 ◇ ((((q0 ◇ (q0 ◇ q1)) ◇ q1) ◇ (((q0 ◇ (q0 ◇ q1)) ◇ q1) ◇ q0)) ◇ q0)) q1).symm)
  have apc2 : forall (q2:G), (q2 ◇ (q2 ◇ (q2 ◇ q2))) = (q2 ◇ (q2 ◇ q2)):=by
    intro q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q2 ◇ q2))) ((h q2 (q2 ◇ (q2 ◇ q2)) q2).symm)).symm).trans (apc0 (q2 ◇ (q2 ◇ q2)) q2)
  have apc3 : forall (q3:G), (((q3 ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ q3) = q3:=by
    intro q3
    exact ((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q3 ◇ q3)) (apc2 q3))).symm).trans (apc0 q3 (q3 ◇ q3))
  have apc5 : forall (q3:G), (((q3 ◇ (q3 ◇ q3)) ◇ (q3 ◇ (q3 ◇ q3))) ◇ q3) = q3:=by
    intro q3
    exact ((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q3 ◇ (q3 ◇ q3))) (apc2 q3))).symm).trans (((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q3 ◇ (q3 ◇ q3))) (cg (fun t => q3 ◇ t) (apc2 q3)))).symm).trans (apc0 q3 (q3 ◇ (q3 ◇ q3))))
  have apc11 : forall (q4 q5:G), ((q5 ◇ q5) ◇ ((q5 ◇ (q5 ◇ q4)) ◇ q4)) = ((q5 ◇ (q5 ◇ q4)) ◇ q4):=by
    intro q4 q5
    exact ((cg (fun t => t ◇ ((q5 ◇ (q5 ◇ q4)) ◇ q4)) (cg (fun t => t ◇ q5) (apc0 q5 q4))).symm).trans (((cg (fun t => t ◇ ((q5 ◇ (q5 ◇ q4)) ◇ q4)) (cg (fun t => t ◇ q5) (cg (fun t => ((q5 ◇ (q5 ◇ q4)) ◇ q4) ◇ t) (apc0 q5 q4)))).symm).trans (apc0 ((q5 ◇ (q5 ◇ q4)) ◇ q4) q5))
  have apc13 : forall (q6 q7 q8:G), ((q7 ◇ (q8 ◇ q8)) ◇ ((q8 ◇ (q8 ◇ q6)) ◇ q6)) = ((q8 ◇ (q8 ◇ q6)) ◇ q6):=by
    intro q6 q7 q8
    exact ((cg (fun t => t ◇ ((q8 ◇ (q8 ◇ q6)) ◇ q6)) (cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q8) (apc0 q8 q6)))).symm).trans (((cg (fun t => t ◇ ((q8 ◇ (q8 ◇ q6)) ◇ q6)) (cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => ((q8 ◇ (q8 ◇ q6)) ◇ q6) ◇ t) (apc0 q8 q6))))).symm).trans ((h ((q8 ◇ (q8 ◇ q6)) ◇ q6) q7 q8).symm))
  have apc14 : forall (q9 q10 q2:G), ((((q9 ◇ ((q2 ◇ (q2 ◇ q10)) ◇ q10)) ◇ q2) ◇ q2) ◇ (q9 ◇ ((q2 ◇ (q2 ◇ q10)) ◇ q10))) = (q9 ◇ ((q2 ◇ (q2 ◇ q10)) ◇ q10)):=by
    intro q9 q10 q2
    exact ((cg (fun t => t ◇ (q9 ◇ ((q2 ◇ (q2 ◇ q10)) ◇ q10))) (cg (fun t => t ◇ q2) (cg (fun t => (q9 ◇ ((q2 ◇ (q2 ◇ q10)) ◇ q10)) ◇ t) ((h q2 q9 q10).symm)))).symm).trans (apc0 (q9 ◇ ((q2 ◇ (q2 ◇ q10)) ◇ q10)) q2)
  have apc15 : forall (q11 q12:G), ((((q12 ◇ (q12 ◇ q11)) ◇ q11) ◇ ((q12 ◇ (q12 ◇ q11)) ◇ q11)) ◇ (q12 ◇ q12)) = (q12 ◇ q12):=by
    intro q11 q12
    exact ((cg (fun t => t ◇ (q12 ◇ q12)) (cg (fun t => t ◇ ((q12 ◇ (q12 ◇ q11)) ◇ q11)) (apc11 q11 q12))).symm).trans (((cg (fun t => t ◇ (q12 ◇ q12)) (cg (fun t => t ◇ ((q12 ◇ (q12 ◇ q11)) ◇ q11)) (cg (fun t => (q12 ◇ q12) ◇ t) (apc11 q11 q12)))).symm).trans (apc0 (q12 ◇ q12) ((q12 ◇ (q12 ◇ q11)) ◇ q11)))
  have apc16 : forall (q13:G), (((q13 ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13)) = (q13 ◇ q13):=by
    intro q13
    exact ((cg (fun t => t ◇ (q13 ◇ q13)) (cg (fun t => t ◇ (q13 ◇ q13)) (apc2 q13))).symm).trans (((cg (fun t => t ◇ (q13 ◇ q13)) (apc13 (q13 ◇ q13) (q13 ◇ (q13 ◇ (q13 ◇ q13))) q13)).symm).trans (apc15 (q13 ◇ q13) q13))
  have apc19 : forall (q14 q15 q16:G), ((q16 ◇ q16) ◇ (q14 ◇ ((q16 ◇ (q16 ◇ q15)) ◇ q15))) = (q14 ◇ ((q16 ◇ (q16 ◇ q15)) ◇ q15)):=by
    intro q14 q15 q16
    exact ((cg (fun t => t ◇ (q14 ◇ ((q16 ◇ (q16 ◇ q15)) ◇ q15))) (cg (fun t => t ◇ q16) ((h q16 q14 q15).symm))).symm).trans (apc14 q14 q15 q16)
  have apc24 : forall (q17 q18:G), ((q17 ◇ (q18 ◇ q18)) ◇ ((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18))) = ((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18)):=by
    intro q17 q18
    exact ((cg (fun t => t ◇ ((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18))) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q18) (apc3 q18)))).symm).trans (((cg (fun t => t ◇ ((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18))) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => ((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18)) ◇ t) (apc3 q18))))).symm).trans ((h ((q18 ◇ (q18 ◇ q18)) ◇ (q18 ◇ q18)) q17 q18).symm))
  have apc25 : forall (q19 q20:G), ((q20 ◇ (q19 ◇ q19)) ◇ (q19 ◇ (q19 ◇ q19))) = (q19 ◇ (q19 ◇ q19)):=by
    intro q19 q20
    exact ((cg (fun t => t ◇ (q19 ◇ (q19 ◇ q19))) (cg (fun t => q20 ◇ t) (apc16 q19))).symm).trans (((cg (fun t => t ◇ (q19 ◇ (q19 ◇ q19))) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ (q19 ◇ q19)) (apc24 q19 q19)))).symm).trans ((h (q19 ◇ (q19 ◇ q19)) q20 (q19 ◇ q19)).symm))
  have apc26 : forall (q19 q20 q3:G), ((q3 ◇ (q3 ◇ q3)) ◇ q3) = q3:=by
    intro q19 q20 q3
    exact ((cg (fun t => t ◇ q3) (apc25 q3 q3)).symm).trans (apc5 q3)
  have apc29 : forall (q21:G), (q21 ◇ q21) = q21:=by
    intro q21
    exact ((cg (fun t => t ◇ q21) (apc26 q21 q21 q21)).symm).trans (apc0 q21 q21)
  have apc31 : forall (q22 q23:G), (q23 ◇ (q22 ◇ q23)) = (q22 ◇ q23):=by
    intro q22 q23
    exact ((cg (fun t => t ◇ (q22 ◇ q23)) (apc29 q23)).symm).trans ((((cg (fun t => (q23 ◇ q23) ◇ t) (cg (fun t => q22 ◇ t) (apc26 q22 q22 q23))).symm).trans (apc19 q22 q23 q23)).trans (((cg (fun t => q22 ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc29 q23)))).trans (cg (fun t => q22 ◇ t) (cg (fun t => t ◇ q23) (apc29 q23)))).trans (cg (fun t => q22 ◇ t) (apc29 q23))))
  have apc32 : forall (q24 q25 q26:G), ((q26 ◇ (q24 ◇ q25)) ◇ q25) = q25:=by
    intro q24 q25 q26
    exact (((cg (fun t => t ◇ q25) (cg (fun t => q26 ◇ t) (cg (fun t => t ◇ (q24 ◇ q25)) (apc31 q24 q25)))).trans (cg (fun t => t ◇ q25) (cg (fun t => q26 ◇ t) (apc29 (q24 ◇ q25))))).symm).trans (((cg (fun t => t ◇ q25) (cg (fun t => q26 ◇ t) (cg (fun t => t ◇ (q24 ◇ q25)) (cg (fun t => q25 ◇ t) (apc31 q24 q25))))).symm).trans ((h q25 q26 (q24 ◇ q25)).symm))
  have apc33 : forall (q27 q28 q29:G), ((q28 ◇ q29) ◇ q27) = q27:=by
    intro q27 q28 q29
    exact ((cg (fun t => t ◇ q27) (cg (fun t => q28 ◇ t) (apc32 q27 q29 q27))).symm).trans ((h q27 q28 q29).symm)
  exact (apc33 x (y ◇ y) y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32113_to_283 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32113_to_283
