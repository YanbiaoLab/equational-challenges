-- Equation5069 → Equation52047
-- Recorded verdict: true
-- Premise: x = y * (y * (x * (z * (x * x))))
-- Conclusion: x * y = ((z * w) * (u * v)) * y
-- Original submission SHA-256: 97988d6f2f4348efb832c74840276fb4e8925a1f382270cac46b86c85607cfc4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (x ◇ (z ◇ (x ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ (u ◇ v)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) ((h q0 (q0 ◇ q0) (q0 ◇ q0)).symm)).symm).trans ((h (q0 ◇ q0) (q0 ◇ q0) q0).symm)
  have apc1 : forall (x y z:G), (y ◇ (y ◇ (x ◇ (z ◇ (x ◇ x))))) = (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (x y z:G), (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc1 x x x)).symm
  have apc4 : forall (q1 q2 q3:G), (q3 ◇ (q3 ◇ ((q1 ◇ (q2 ◇ (q1 ◇ q1))) ◇ q1))) = (q1 ◇ (q2 ◇ (q1 ◇ q1))):=by
    intro q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => (q1 ◇ (q2 ◇ (q1 ◇ q1))) ◇ t) ((h q1 (q1 ◇ (q2 ◇ (q1 ◇ q1))) q2).symm)))).symm).trans ((h (q1 ◇ (q2 ◇ (q1 ◇ q1))) q3 (q1 ◇ (q2 ◇ (q1 ◇ q1)))).symm)
  have apc6 : forall (q4 q5 q6:G), (q6 ◇ (q6 ◇ (((q4 ◇ (q5 ◇ (q4 ◇ q4))) ◇ q4) ◇ (q4 ◇ (q5 ◇ (q4 ◇ q4)))))) = ((q4 ◇ (q5 ◇ (q4 ◇ q4))) ◇ q4):=by
    intro q4 q5 q6
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => ((q4 ◇ (q5 ◇ (q4 ◇ q4))) ◇ q4) ◇ t) (apc4 q4 q5 ((q4 ◇ (q5 ◇ (q4 ◇ q4))) ◇ q4))))).symm).trans ((h ((q4 ◇ (q5 ◇ (q4 ◇ q4))) ◇ q4) q6 ((q4 ◇ (q5 ◇ (q4 ◇ q4))) ◇ q4)).symm)
  have apc9 : forall (q7 q8:G), ((((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) = (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))):=by
    intro q7 q8
    exact ((cg (fun t => (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) ◇ t) (apc4 q7 q8 (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))))).symm).trans (((cg (fun t => (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) ◇ t) (cg (fun t => (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) ◇ t) (cg (fun t => (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) ◇ t) (apc6 q7 q8 (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))))))).symm).trans (apc2 (((q7 ◇ (q8 ◇ (q7 ◇ q7))) ◇ q7) ◇ (q7 ◇ (q8 ◇ (q7 ◇ q7)))) q7 q7))
  have apc19 : forall (q9 q10:G), ((((q9 ◇ (q10 ◇ (q9 ◇ q9))) ◇ q9) ◇ (q9 ◇ (q10 ◇ (q9 ◇ q9)))) ◇ (((q9 ◇ (q10 ◇ (q9 ◇ q9))) ◇ q9) ◇ (q9 ◇ (q10 ◇ (q9 ◇ q9))))) = q9:=by
    intro q9 q10
    exact ((cg (fun t => (((q9 ◇ (q10 ◇ (q9 ◇ q9))) ◇ q9) ◇ (q9 ◇ (q10 ◇ (q9 ◇ q9)))) ◇ t) (apc9 q9 q10)).symm).trans ((h q9 (((q9 ◇ (q10 ◇ (q9 ◇ q9))) ◇ q9) ◇ (q9 ◇ (q10 ◇ (q9 ◇ q9)))) q10).symm)
  have apc20 : forall (q11 q12:G), (q11 ◇ (((q11 ◇ (q12 ◇ (q11 ◇ q11))) ◇ q11) ◇ (q11 ◇ (q12 ◇ (q11 ◇ q11))))) = q11:=by
    intro q11 q12
    exact (((cg (fun t => t ◇ (((q11 ◇ (q12 ◇ (q11 ◇ q11))) ◇ q11) ◇ (q11 ◇ (q12 ◇ (q11 ◇ q11))))) (apc19 q11 q12)).symm).trans (apc0 (((q11 ◇ (q12 ◇ (q11 ◇ q11))) ◇ q11) ◇ (q11 ◇ (q12 ◇ (q11 ◇ q11)))))).trans (apc19 q11 q12)
  have apc21 : forall (q13 q14:G), ((q13 ◇ (q14 ◇ (q13 ◇ q13))) ◇ q13) = (q13 ◇ q13):=by
    intro q13 q14
    exact (((cg (fun t => q13 ◇ t) (apc20 q13 q14)).symm).trans (apc6 q13 q14 q13)).symm
  have apc22 : forall (q1 q2 q3 q13 q14:G), (q3 ◇ (q3 ◇ (q1 ◇ q1))) = (q1 ◇ (q2 ◇ (q1 ◇ q1))):=by
    intro q1 q2 q3 q13 q14
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (apc21 q1 q2))).symm).trans (apc4 q1 q2 q3)
  have apc23 : forall (q1 q2 q3 q13 q14:G), (q1 ◇ (q2 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q1 q2 q3 q13 q14
    exact ((apc22 q1 q2 q1 q1 q1).symm).trans (apc22 q1 q1 q1 q1 q1)
  have apc24 : forall (q1 q2 q3 q13 q14:G), (q3 ◇ (q3 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q1 q2 q3 q13 q14
    exact (apc22 q1 q1 q3 q1 q1).trans ((apc22 q1 q1 q1 q1 q1).symm)
  have apc26 : forall (q15 q16 q17:G), (q17 ◇ (q17 ◇ (q15 ◇ (q15 ◇ (q16 ◇ q16))))) = q16:=by
    intro q15 q16 q17
    exact ((cg (fun t => q17 ◇ t) (cg (fun t => q17 ◇ t) ((apc22 q16 q15 q15 q15 q15).symm))).symm).trans ((h q16 q17 q15).symm)
  have apc34 : forall (q18 q19:G), (q19 ◇ (q19 ◇ (q18 ◇ (q18 ◇ (q18 ◇ (q18 ◇ q18)))))) = (q18 ◇ q18):=by
    intro q18 q19
    exact ((cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => q18 ◇ t) (apc23 q18 (q18 ◇ q18) q18 q18 q18)))).symm).trans (apc26 q18 (q18 ◇ q18) q19)
  have apc35 : forall (q20 q21:G), ((q20 ◇ q20) ◇ (q20 ◇ q20)) = (q21 ◇ (q21 ◇ q20)):=by
    intro q20 q21
    exact (((cg (fun t => q21 ◇ t) (cg (fun t => q21 ◇ t) (apc26 (q20 ◇ q20) q20 (q20 ◇ q20)))).symm).trans (apc34 (q20 ◇ q20) q21)).symm
  have apc36 : forall (q20 q21:G), (q21 ◇ (q21 ◇ q20)) = (q20 ◇ (q20 ◇ q20)):=by
    intro q20 q21
    exact ((apc35 q20 q21).symm).trans (apc35 q20 q20)
  have apc38 : forall (q20 q21:G), ((q20 ◇ q20) ◇ (q20 ◇ q20)) = (q20 ◇ (q20 ◇ q20)):=by
    intro q20 q21
    exact (apc35 q20 q20).trans (apc36 q20 q20)
  have apc42 : forall (q22 q23:G), ((q23 ◇ q23) ◇ (q22 ◇ (q22 ◇ q23))) = (q23 ◇ (q23 ◇ (q23 ◇ q23))):=by
    intro q22 q23
    exact ((cg (fun t => (q23 ◇ q23) ◇ t) (apc35 q23 q22)).symm).trans (apc24 q23 q22 (q23 ◇ q23) q22 q22)
  have apc54 : forall (q24 q25:G), ((q25 ◇ q24) ◇ ((q25 ◇ q24) ◇ (q25 ◇ q24))) = (q25 ◇ (q24 ◇ (q24 ◇ q24))):=by
    intro q24 q25
    exact (((cg (fun t => q25 ◇ t) (apc36 q24 q25)).symm).trans (apc36 (q25 ◇ q24) q25)).symm
  have apc55 : forall (q26 q27:G), (q26 ◇ (q27 ◇ (q26 ◇ (q26 ◇ (q26 ◇ q26))))) = q26:=by
    intro q26 q27
    exact ((((cg (fun t => q26 ◇ t) (apc54 (q26 ◇ q26) q27)).trans (cg (fun t => q26 ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => (q26 ◇ q26) ◇ t) (apc38 q26 ((q26 ◇ q26) ◇ (q26 ◇ q26))))))).trans (cg (fun t => q26 ◇ t) (cg (fun t => q27 ◇ t) (apc42 q26 q26)))).symm).trans (((apc54 (q27 ◇ (q26 ◇ q26)) q26).symm).trans ((h q26 (q26 ◇ (q27 ◇ (q26 ◇ q26))) q27).symm))
  have apc56 : forall (q28 q29:G), (q29 ◇ q29) = (q28 ◇ q29):=by
    intro q28 q29
    exact (((cg (fun t => q29 ◇ t) (apc55 q29 q28)).symm).trans (apc36 (q28 ◇ (q29 ◇ (q29 ◇ (q29 ◇ q29)))) q29)).trans ((apc54 (q29 ◇ (q29 ◇ (q29 ◇ q29))) q28).trans (cg (fun t => q28 ◇ t) (apc26 q29 q29 (q29 ◇ (q29 ◇ (q29 ◇ q29))))))
  exact ((apc56 x y).symm).trans (apc56 ((z ◇ w) ◇ (u ◇ v)) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5069_to_52047 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5069_to_52047
