-- Equation22780 → Equation32033
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ x)) ◇ ((z ◇ y) ◇ z)
-- Conclusion: x = (x ◇ ((y ◇ (z ◇ y)) ◇ z)) ◇ x
-- Original submission SHA-256: d6a1bccc4550723e44cfd5a1bf823f97919c93194519c75691ff01433b093056
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ ((z ◇ y) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ (z ◇ y)) ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2:G), (q0 ◇ (((q2 ◇ q1) ◇ (q1 ◇ (q2 ◇ q0))) ◇ (q2 ◇ q1))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (((q2 ◇ q1) ◇ (q1 ◇ (q2 ◇ q0))) ◇ (q2 ◇ q1))) ((h q0 q1 q2).symm)).symm).trans ((h q2 (q1 ◇ (q2 ◇ q0)) (q2 ◇ q1)).symm)
  have apc3 : forall (q3 q4:G), (q4 ◇ (q3 ◇ (q3 ◇ ((q3 ◇ q4) ◇ q3)))) = q3:=by
    intro q3 q4
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q3 ◇ ((q3 ◇ q4) ◇ q3))) ((h q3 q3 (q3 ◇ q4)).symm))).symm).trans (apc2 q4 ((q3 ◇ q4) ◇ q3) q3)
  have apc4 : forall (q5 q6 q7:G), (q5 ◇ (q5 ◇ ((q5 ◇ q7) ◇ q5))) = ((q6 ◇ q5) ◇ ((q7 ◇ q6) ◇ q7)):=by
    intro q5 q6 q7
    exact (((cg (fun t => t ◇ ((q7 ◇ q6) ◇ q7)) (cg (fun t => q6 ◇ t) (apc3 q5 q7))).symm).trans ((h (q5 ◇ (q5 ◇ ((q5 ◇ q7) ◇ q5))) q6 q7).symm)).symm
  have apc5 : forall (q8 q9 q10:G), (q10 ◇ ((q8 ◇ q9) ◇ ((q10 ◇ q8) ◇ q10))) = q9:=by
    intro q8 q9 q10
    exact ((cg (fun t => q10 ◇ t) (apc4 q9 q8 q10)).symm).trans (apc3 q9 q10)
  have apc10 : forall (q11:G), (((q11 ◇ (q11 ◇ q11)) ◇ q11) ◇ (q11 ◇ (q11 ◇ q11))) = q11:=by
    intro q11
    exact ((cg (fun t => ((q11 ◇ (q11 ◇ q11)) ◇ q11) ◇ t) (cg (fun t => t ◇ (q11 ◇ q11)) (apc3 q11 (q11 ◇ q11)))).symm).trans (apc2 ((q11 ◇ (q11 ◇ q11)) ◇ q11) q11 q11)
  have apc11 : forall (q12 q13:G), ((q13 ◇ ((q13 ◇ (q13 ◇ q13)) ◇ q12)) ◇ q13) = q12:=by
    intro q12 q13
    exact ((cg (fun t => (q13 ◇ ((q13 ◇ (q13 ◇ q13)) ◇ q12)) ◇ t) (apc10 q13)).symm).trans ((h q12 q13 (q13 ◇ (q13 ◇ q13))).symm)
  have apc12 : forall (q14 q15:G), ((q14 ◇ (q14 ◇ q14)) ◇ ((q14 ◇ q15) ◇ q14)) = q15:=by
    intro q14 q15
    exact ((cg (fun t => (q14 ◇ (q14 ◇ q14)) ◇ t) (cg (fun t => (q14 ◇ q15) ◇ t) (apc10 q14))).symm).trans (apc5 q14 q15 (q14 ◇ (q14 ◇ q14)))
  have apc14 : forall (q16 q17 q18:G), (q17 ◇ (((q16 ◇ q17) ◇ q18) ◇ (q16 ◇ q17))) = ((q18 ◇ q16) ◇ q18):=by
    intro q16 q17 q18
    exact ((cg (fun t => t ◇ (((q16 ◇ q17) ◇ q18) ◇ (q16 ◇ q17))) (apc5 q16 q17 q18)).symm).trans ((h ((q18 ◇ q16) ◇ q18) q18 (q16 ◇ q17)).symm)
  have apc15 : forall (q19 q20:G), ((q20 ◇ ((q19 ◇ (q19 ◇ q19)) ◇ q19)) ◇ q20) = q20:=by
    intro q19 q20
    exact ((((cg (fun t => (q19 ◇ (q19 ◇ q19)) ◇ t) (cg (fun t => (q19 ◇ q20) ◇ t) (apc10 q19))).trans (apc12 q19 q20)).symm).trans (((cg (fun t => (q19 ◇ (q19 ◇ q19)) ◇ t) (cg (fun t => t ◇ (((q19 ◇ (q19 ◇ q19)) ◇ q19) ◇ (q19 ◇ (q19 ◇ q19)))) (cg (fun t => t ◇ q20) (apc10 q19)))).symm).trans (apc14 ((q19 ◇ (q19 ◇ q19)) ◇ q19) (q19 ◇ (q19 ◇ q19)) q20))).symm
  have apc26 : forall (q21 q22 q23:G), ((((q23 ◇ (q23 ◇ q23)) ◇ q21) ◇ (q23 ◇ q22)) ◇ q21) = q22:=by
    intro q21 q22 q23
    exact ((cg (fun t => (((q23 ◇ (q23 ◇ q23)) ◇ q21) ◇ (q23 ◇ q22)) ◇ t) (apc11 q21 q23)).symm).trans ((h q22 ((q23 ◇ (q23 ◇ q23)) ◇ q21) q23).symm)
  have apc27 : forall (q24 q25:G), (q25 ◇ (q25 ◇ q25)) = (q24 ◇ (q25 ◇ q24)):=by
    intro q24 q25
    exact (((cg (fun t => t ◇ (q25 ◇ q24)) (apc26 ((q25 ◇ (q25 ◇ q25)) ◇ (q25 ◇ (q25 ◇ q25))) q24 q25)).symm).trans (apc26 (q25 ◇ q24) (q25 ◇ (q25 ◇ q25)) (q25 ◇ (q25 ◇ q25)))).symm
  have apc49 : forall (q26 q27 q28:G), ((q28 ◇ ((q26 ◇ (q27 ◇ q26)) ◇ q27)) ◇ q28) = q28:=by
    intro q26 q27 q28
    exact ((cg (fun t => t ◇ q28) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ q27) (apc27 q26 q27)))).symm).trans (apc15 q27 q28)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ ((y ◇ (z ◇ y)) ◇ z)) ◇ x):=(apc49 y z x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22780_to_32033 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22780_to_32033
