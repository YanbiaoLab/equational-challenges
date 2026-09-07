-- Equation19387 → Equation24022
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ ((z ◇ x) ◇ (x ◇ y))
-- Conclusion: x = ((x ◇ x) ◇ y) ◇ ((y ◇ z) ◇ z)
-- Original submission SHA-256: 71e231b5b4a7acfb2099f34842a0d628d05084ae52baae6e31a9b44f4ad34be9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ x) ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ x) ◇ y) ◇ ((y ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ z) ◇ ((z ◇ x) ◇ (x ◇ y))) = ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (q0 ◇ ((((q2 ◇ q0) ◇ (q0 ◇ q1)) ◇ q3) ◇ (q3 ◇ (q1 ◇ q2)))) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((((q2 ◇ q0) ◇ (q0 ◇ q1)) ◇ q3) ◇ (q3 ◇ (q1 ◇ q2)))) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) ((q2 ◇ q0) ◇ (q0 ◇ q1))).symm)
  have apc3 : forall (q0 q1 q2 q4:G), ((((q2 ◇ q0) ◇ (q0 ◇ q1)) ◇ q4) ◇ ((q4 ◇ (q1 ◇ q2)) ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q4
    exact ((cg (fun t => (((q2 ◇ q0) ◇ (q0 ◇ q1)) ◇ q4) ◇ t) (cg (fun t => (q4 ◇ (q1 ◇ q2)) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ q2) ((q2 ◇ q0) ◇ (q0 ◇ q1)) q4).symm)
  have apc6 : forall (q5 q6 q7 q8:G), (((((q5 ◇ q6) ◇ q8) ◇ (q8 ◇ (q7 ◇ q5))) ◇ (q6 ◇ q7)) ◇ (q5 ◇ q8)) = ((q7 ◇ q5) ◇ (q5 ◇ q6)):=by
    intro q5 q6 q7 q8
    exact ((cg (fun t => ((((q5 ◇ q6) ◇ q8) ◇ (q8 ◇ (q7 ◇ q5))) ◇ (q6 ◇ q7)) ◇ t) (cg (fun t => t ◇ q8) ((h q5 q6 q7).symm))).symm).trans (apc3 q8 (q7 ◇ q5) (q5 ◇ q6) (q6 ◇ q7))
  have apc9 : forall (q9 q10 q11 q12 q13:G), (q11 ◇ ((((((q10 ◇ q13) ◇ (q13 ◇ q9)) ◇ q11) ◇ (q11 ◇ (q9 ◇ q10))) ◇ q12) ◇ (q12 ◇ q13))) = q12:=by
    intro q9 q10 q11 q12 q13
    exact ((cg (fun t => t ◇ ((((((q10 ◇ q13) ◇ (q13 ◇ q9)) ◇ q11) ◇ (q11 ◇ (q9 ◇ q10))) ◇ q12) ◇ (q12 ◇ q13))) (apc2 q13 q9 q10 q11)).symm).trans ((h q12 q13 ((((q10 ◇ q13) ◇ (q13 ◇ q9)) ◇ q11) ◇ (q11 ◇ (q9 ◇ q10)))).symm)
  have apc10 : forall (q14 q15:G), (((q15 ◇ (q14 ◇ q15)) ◇ ((q14 ◇ q15) ◇ q14)) ◇ ((q15 ◇ (q14 ◇ q15)) ◇ ((q14 ◇ q15) ◇ q14))) = (q14 ◇ q15):=by
    intro q14 q15
    exact ((cg (fun t => ((q15 ◇ (q14 ◇ q15)) ◇ ((q14 ◇ q15) ◇ q14)) ◇ t) (apc6 (q14 ◇ q15) q14 q15 ((q15 ◇ (q14 ◇ q15)) ◇ ((q14 ◇ q15) ◇ q14)))).symm).trans (apc2 ((q15 ◇ (q14 ◇ q15)) ◇ ((q14 ◇ q15) ◇ q14)) (q15 ◇ (q14 ◇ q15)) ((q14 ◇ q15) ◇ q14) (q14 ◇ q15))
  have apc11 : forall (q16 q17:G), ((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16)) = ((q16 ◇ q17) ◇ ((q16 ◇ q17) ◇ (q16 ◇ q17))):=by
    intro q16 q17
    exact ((((cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => t ◇ (((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16)) ◇ ((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16)))) (apc10 q16 q17))).trans (cg (fun t => (q16 ◇ q17) ◇ t) (cg (fun t => (q16 ◇ q17) ◇ t) (apc10 q16 q17)))).symm).trans (((cg (fun t => t ◇ ((((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16)) ◇ ((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16))) ◇ (((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16)) ◇ ((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16))))) (apc10 q16 q17)).symm).trans (apc1 ((q17 ◇ (q16 ◇ q17)) ◇ ((q16 ◇ q17) ◇ q16)) q16 q16))).symm
  have apc12 : forall (q18:G), (q18 ◇ (q18 ◇ (q18 ◇ q18))) = q18:=by
    intro q18
    exact ((((cg (fun t => q18 ◇ t) (cg (fun t => (q18 ◇ ((((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ q18) ◇ (q18 ◇ (q18 ◇ q18)))) ◇ t) (cg (fun t => t ◇ (q18 ◇ ((((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ q18) ◇ (q18 ◇ (q18 ◇ q18))))) (apc2 q18 q18 q18 q18)))).trans (cg (fun t => q18 ◇ t) (cg (fun t => (q18 ◇ ((((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ q18) ◇ (q18 ◇ (q18 ◇ q18)))) ◇ t) (cg (fun t => q18 ◇ t) (apc2 q18 q18 q18 q18))))).trans (cg (fun t => q18 ◇ t) (cg (fun t => t ◇ (q18 ◇ q18)) (apc2 q18 q18 q18 q18)))).symm).trans ((((cg (fun t => q18 ◇ t) (apc11 q18 ((((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ q18) ◇ (q18 ◇ (q18 ◇ q18))))).symm).trans (apc9 q18 q18 q18 (q18 ◇ ((((q18 ◇ q18) ◇ (q18 ◇ q18)) ◇ q18) ◇ (q18 ◇ (q18 ◇ q18)))) q18)).trans (apc2 q18 q18 q18 q18))
  have apc13 : forall (q19:G), ((q19 ◇ q19) ◇ q19) = (q19 ◇ q19):=by
    intro q19
    exact ((cg (fun t => (q19 ◇ q19) ◇ t) ((h q19 q19 q19).symm)).symm).trans (apc12 (q19 ◇ q19))
  have apc14 : forall (q20:G), ((q20 ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20)) = q20:=by
    intro q20
    exact (((cg (fun t => (q20 ◇ (q20 ◇ q20)) ◇ t) (apc13 q20)).symm).trans (apc11 q20 q20)).trans (apc1 q20 ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20))) ((q20 ◇ q20) ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20))))
  have apc15 : forall (q21:G), (q21 ◇ (q21 ◇ q21)) = (q21 ◇ q21):=by
    intro q21
    exact ((((((cg (fun t => ((q21 ◇ q21) ◇ q21) ◇ t) (cg (fun t => t ◇ (q21 ◇ (q21 ◇ q21))) (apc14 q21))).trans (cg (fun t => t ◇ (q21 ◇ (q21 ◇ (q21 ◇ q21)))) (apc13 q21))).trans (cg (fun t => (q21 ◇ q21) ◇ t) (apc12 q21))).trans (apc13 q21)).symm).trans ((((cg (fun t => t ◇ (((q21 ◇ (q21 ◇ q21)) ◇ (q21 ◇ q21)) ◇ (q21 ◇ (q21 ◇ q21)))) (cg (fun t => (q21 ◇ q21) ◇ t) (apc14 q21))).symm).trans (apc11 (q21 ◇ (q21 ◇ q21)) (q21 ◇ q21))).trans (((cg (fun t => ((q21 ◇ (q21 ◇ q21)) ◇ (q21 ◇ q21)) ◇ t) (cg (fun t => t ◇ ((q21 ◇ (q21 ◇ q21)) ◇ (q21 ◇ q21))) (apc14 q21))).trans (cg (fun t => ((q21 ◇ (q21 ◇ q21)) ◇ (q21 ◇ q21)) ◇ t) (cg (fun t => q21 ◇ t) (apc14 q21)))).trans (cg (fun t => t ◇ (q21 ◇ q21)) (apc14 q21))))).symm
  have apc16 : forall (q18 q21:G), (q18 ◇ q18) = q18:=by
    intro q18 q21
    exact (((cg (fun t => q18 ◇ t) (apc15 q18)).trans (apc15 q18)).symm).trans (apc12 q18)
  have apc17 : forall (q22 q23:G), (q23 ◇ ((q23 ◇ q22) ◇ (q22 ◇ q23))) = q22:=by
    intro q22 q23
    exact ((cg (fun t => t ◇ ((q23 ◇ q22) ◇ (q22 ◇ q23))) (apc16 q23 q22)).symm).trans ((h q22 q23 q23).symm)
  have apc18 : forall (q22 q24:G), ((q24 ◇ q22) ◇ (q22 ◇ (q22 ◇ q24))) = q22:=by
    intro q22 q24
    exact ((cg (fun t => (q24 ◇ q22) ◇ t) (cg (fun t => t ◇ (q22 ◇ q24)) (apc16 q22 q22))).symm).trans ((h q22 q24 q22).symm)
  have apc19 : forall (q25 q26:G), (((q25 ◇ q26) ◇ q26) ◇ q25) = q25:=by
    intro q25 q26
    exact ((cg (fun t => ((q25 ◇ q26) ◇ q26) ◇ t) (apc18 q25 q26)).symm).trans ((h q25 (q25 ◇ q26) q26).symm)
  have apc21 : forall (q27 q28:G), (q28 ◇ ((q28 ◇ q27) ◇ q27)) = ((q28 ◇ q27) ◇ q27):=by
    intro q27 q28
    exact ((cg (fun t => t ◇ ((q28 ◇ q27) ◇ q27)) (apc16 q28 (q28 ◇ q28))).symm).trans (((cg (fun t => t ◇ ((q28 ◇ q27) ◇ q27)) (cg (fun t => t ◇ q28) (apc19 q28 q27))).symm).trans (apc19 ((q28 ◇ q27) ◇ q27) q28))
  have apc22 : forall (q29 q30:G), ((q30 ◇ q29) ◇ q29) = q30:=by
    intro q29 q30
    exact (((((cg (fun t => q30 ◇ t) (cg (fun t => ((q30 ◇ q29) ◇ q29) ◇ t) (apc19 q30 q29))).trans (cg (fun t => q30 ◇ t) (apc19 q30 q29))).trans (apc16 q30 (q30 ◇ q30))).symm).trans (((cg (fun t => q30 ◇ t) (cg (fun t => t ◇ (((q30 ◇ q29) ◇ q29) ◇ q30)) (apc21 q29 q30))).symm).trans (apc17 ((q30 ◇ q29) ◇ q29) q30))).symm
  exact (calc
    x = x:=rfl
    _ = (((x ◇ x) ◇ y) ◇ ((y ◇ z) ◇ z)):=(((cg (fun t => t ◇ ((y ◇ z) ◇ z)) (cg (fun t => t ◇ y) (apc16 x (x ◇ x)))).trans (cg (fun t => (x ◇ y) ◇ t) (apc22 z y))).trans (apc22 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19387_to_24022 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19387_to_24022
