-- Equation29648 → Equation48148
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ (y ◇ (x ◇ z)))) ◇ x
-- Conclusion: x ◇ y = (y ◇ (z ◇ w)) ◇ (x ◇ y)
-- Original submission SHA-256: 1d8205909378c9ce5a025aab3675155637db2367395aacd5d6775c983dac1886
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ (y ◇ (x ◇ z)))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (z ◇ w)) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (y ◇ (y ◇ (x ◇ z)))) ◇ x) = ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc2 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q2 ◇ (q2 ◇ q3))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q3 ◇ q1))))) = (q0 ◇ (q0 ◇ (q0 ◇ (q3 ◇ q1)))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q3 ◇ q1))))) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q3 q0 q1).symm))))).symm).trans ((h (q0 ◇ (q0 ◇ (q0 ◇ (q3 ◇ q1)))) q2 q3).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((q6 ◇ (q6 ◇ (q6 ◇ (q5 ◇ q4)))) ◇ q6) = q6:=by
    intro q4 q5 q6 q7
    exact (((cg (fun t => t ◇ q6) (cg (fun t => (q7 ◇ (q7 ◇ (q7 ◇ q5))) ◇ t) (apc2 q6 q4 q7 q5))).trans (cg (fun t => t ◇ q6) (apc2 q6 q4 q7 q5))).symm).trans (((cg (fun t => t ◇ q6) (cg (fun t => (q7 ◇ (q7 ◇ (q7 ◇ q5))) ◇ t) (cg (fun t => (q7 ◇ (q7 ◇ (q7 ◇ q5))) ◇ t) (apc2 q6 q4 q7 q5)))).symm).trans ((h q6 (q7 ◇ (q7 ◇ (q7 ◇ q5))) (q6 ◇ (q6 ◇ (q5 ◇ q4)))).symm))
  have apc4 : forall (q8 q9:G), ((q9 ◇ (q9 ◇ (q9 ◇ q8))) ◇ q9) = q9:=by
    intro q8 q9
    exact ((cg (fun t => t ◇ q9) (cg (fun t => q9 ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => q9 ◇ t) ((h q8 q8 q8).symm))))).symm).trans (apc3 q8 (q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8)))) q9 q8)
  have apc5 : forall (q10 q11 q12:G), ((q10 ◇ q11) ◇ q10) = q10:=by
    intro q10 q11 q12
    exact (((cg (fun t => t ◇ q10) (cg (fun t => ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ q12))) ◇ t) (apc4 q12 (q10 ◇ q11)))).trans (cg (fun t => t ◇ q10) (apc4 q12 (q10 ◇ q11)))).symm).trans (((cg (fun t => t ◇ q10) (cg (fun t => ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ q12))) ◇ t) (cg (fun t => ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ q12))) ◇ t) (apc4 q12 (q10 ◇ q11))))).symm).trans ((h q10 ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ ((q10 ◇ q11) ◇ q12))) q11).symm))
  have apc6 : forall (q13 q14 q15:G), ((q14 ◇ (q14 ◇ (q14 ◇ q15))) ◇ (q15 ◇ q13)) = (q15 ◇ q13):=by
    intro q13 q14 q15
    exact ((cg (fun t => t ◇ (q15 ◇ q13)) (cg (fun t => q14 ◇ t) (cg (fun t => q14 ◇ t) (cg (fun t => q14 ◇ t) (apc5 q15 q13 q13))))).symm).trans ((h (q15 ◇ q13) q14 q15).symm)
  have apc7 : forall (q16 q17:G), (q17 ◇ (q17 ◇ q16)) = (q17 ◇ q16):=by
    intro q16 q17
    exact ((cg (fun t => t ◇ (q17 ◇ q16)) (apc5 q17 q16 q16)).symm).trans (apc5 (q17 ◇ q16) q17 q16)
  have apc8 : forall (q13 q14 q15 q16 q17:G), ((q14 ◇ q15) ◇ (q15 ◇ q13)) = (q15 ◇ q13):=by
    intro q13 q14 q15 q16 q17
    exact (((cg (fun t => t ◇ (q15 ◇ q13)) (cg (fun t => q14 ◇ t) (apc7 q15 q14))).trans (cg (fun t => t ◇ (q15 ◇ q13)) (apc7 q15 q14))).symm).trans (apc6 q13 q14 q15)
  have apc9 : forall (q18 q19 q20 q21:G), ((q21 ◇ (q20 ◇ q18)) ◇ (q19 ◇ q20)) = (q19 ◇ q20):=by
    intro q18 q19 q20 q21
    exact (((cg (fun t => t ◇ (q19 ◇ q20)) (cg (fun t => q21 ◇ t) (apc7 (q20 ◇ q18) q21))).trans (cg (fun t => t ◇ (q19 ◇ q20)) (apc7 (q20 ◇ q18) q21))).symm).trans (((cg (fun t => t ◇ (q19 ◇ q20)) (cg (fun t => q21 ◇ t) (cg (fun t => q21 ◇ t) (cg (fun t => q21 ◇ t) (apc8 q18 q19 q20 q18 q18))))).symm).trans ((h (q19 ◇ q20) q21 (q20 ◇ q18)).symm))
  have apc10 : forall (q22 q23 q24 q25:G), ((q24 ◇ q25) ◇ (q22 ◇ (q25 ◇ q23))) = (q22 ◇ (q25 ◇ q23)):=by
    intro q22 q23 q24 q25
    exact (((((((((cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23))))) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => q25 ◇ t) (cg (fun t => q25 ◇ t) (apc7 q25 q25)))))))).trans (cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23))))) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q25) (cg (fun t => q25 ◇ t) (apc7 q25 q25)))))))).trans (cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23))))) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q25) (apc7 q25 q25))))))).trans (cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23))))) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (apc5 q25 q25 ((q25 ◇ q25) ◇ q25))))))).trans (cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23))))) (cg (fun t => q24 ◇ t) (apc7 q25 q24)))).trans (cg (fun t => (q24 ◇ (q24 ◇ q25)) ◇ t) (cg (fun t => q22 ◇ t) (apc7 (q25 ◇ q23) q22)))).trans (cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23)))) (apc7 q25 q24))).trans (cg (fun t => (q24 ◇ q25) ◇ t) (apc7 (q25 ◇ q23) q22))).symm).trans ((((cg (fun t => t ◇ (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23))))) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => q24 ◇ t) (apc0 q25 q22 q23))))).symm).trans ((h (q22 ◇ (q22 ◇ (q22 ◇ (q25 ◇ q23)))) q24 q25).symm)).trans ((cg (fun t => q22 ◇ t) (apc7 (q25 ◇ q23) q22)).trans (apc7 (q25 ◇ q23) q22)))
  have apc11 : forall (q26 q27 q28 q29:G), ((q29 ◇ (q27 ◇ q26)) ◇ (q28 ◇ q29)) = (q28 ◇ q29):=by
    intro q26 q27 q28 q29
    exact ((cg (fun t => t ◇ (q28 ◇ q29)) (apc10 q29 q26 q26 q27)).symm).trans (apc9 (q27 ◇ q26) q28 q29 (q26 ◇ q27))
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = ((y ◇ (z ◇ w)) ◇ (x ◇ y)):=(apc11 w z x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29648_to_48148 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29648_to_48148
