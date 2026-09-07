-- Equation20301 → Equation13721
-- Recorded verdict: true
-- Premise: x = (y * z) * ((z * (z * y)) * x)
-- Conclusion: x = y * ((x * ((y * y) * z)) * x)
-- Original submission SHA-256: ea1fe38e448a848afae5262c2f6d976a3febdb69d33a39e5cb3bbc99185b9cfd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ (z ◇ y)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ ((y ◇ y) ◇ z)) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q1) ◇ ((q2 ◇ q1) ◇ q2)) ◇ q0) = ((q1 ◇ q2) ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q1 ◇ q2) ◇ t) ((h q0 q2 (q2 ◇ q1)).symm)).symm).trans ((h (((q2 ◇ q1) ◇ ((q2 ◇ q1) ◇ q2)) ◇ q0) q1 q2).symm)).symm
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ (q5 ◇ q3)) ◇ ((q3 ◇ q5) ◇ q4)) = q4:=by
    intro q3 q4 q5
    exact ((cg (fun t => (q5 ◇ (q5 ◇ q3)) ◇ t) (apc0 q4 q3 q5)).symm).trans ((h q4 q5 (q5 ◇ q3)).symm)
  have apc2 : forall (x y z:G), ((y ◇ z) ◇ ((z ◇ (z ◇ y)) ◇ x)) = ((x ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc3 : forall (x y z:G), ((x ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) = x:=by
    intro x y z
    exact ((h x x x).trans (apc2 x x x)).symm
  have apc4 : forall (q6 q7 q8:G), ((((q7 ◇ q6) ◇ q7) ◇ (q7 ◇ q6)) ◇ q8) = (((q6 ◇ q7) ◇ ((q6 ◇ q7) ◇ (q7 ◇ q6))) ◇ q8):=by
    intro q6 q7 q8
    exact (((cg (fun t => t ◇ q8) (cg (fun t => (q6 ◇ q7) ◇ t) (apc0 (q7 ◇ q6) q6 q7))).symm).trans (((cg (fun t => t ◇ q8) (apc0 (((q7 ◇ q6) ◇ ((q7 ◇ q6) ◇ q7)) ◇ (q7 ◇ q6)) q6 q7)).symm).trans (apc0 q8 ((q7 ◇ q6) ◇ q7) (q7 ◇ q6)))).symm
  have apc8 : forall (q0 q9 q10 q11:G), ((((q10 ◇ (q10 ◇ q9)) ◇ q0) ◇ (q9 ◇ q10)) ◇ (((q9 ◇ q10) ◇ q0) ◇ q11)) = q11:=by
    intro q0 q9 q10 q11
    exact ((cg (fun t => (((q10 ◇ (q10 ◇ q9)) ◇ q0) ◇ (q9 ◇ q10)) ◇ t) (cg (fun t => t ◇ q11) (cg (fun t => (q9 ◇ q10) ◇ t) ((h q0 q9 q10).symm)))).symm).trans ((h q11 ((q10 ◇ (q10 ◇ q9)) ◇ q0) (q9 ◇ q10)).symm)
  have apc9 : forall (q12 q13:G), ((((q12 ◇ q12) ◇ q12) ◇ (q12 ◇ q12)) ◇ (q12 ◇ q13)) = q13:=by
    intro q12 q13
    exact ((cg (fun t => t ◇ (q12 ◇ q13)) (apc0 (q12 ◇ q12) (q12 ◇ q12) q12)).symm).trans (((cg (fun t => (((q12 ◇ (q12 ◇ q12)) ◇ ((q12 ◇ (q12 ◇ q12)) ◇ q12)) ◇ (q12 ◇ q12)) ◇ t) (cg (fun t => t ◇ q13) (apc3 q12 q12 q12))).symm).trans (apc8 ((q12 ◇ (q12 ◇ q12)) ◇ q12) q12 q12 q13))
  have apc11 : forall (q14 q15:G), (((q15 ◇ q15) ◇ ((q15 ◇ q15) ◇ (q15 ◇ q15))) ◇ (q15 ◇ q14)) = q14:=by
    intro q14 q15
    exact (((apc9 q15 q14).symm).trans (apc4 q15 q15 (q15 ◇ q14))).symm
  have apc12 : forall (q16 q17:G), (((q17 ◇ q17) ◇ (q17 ◇ q17)) ◇ q16) = (q17 ◇ q16):=by
    intro q16 q17
    exact ((cg (fun t => ((q17 ◇ q17) ◇ (q17 ◇ q17)) ◇ t) (apc11 q16 q17)).symm).trans ((h (q17 ◇ q16) (q17 ◇ q17) (q17 ◇ q17)).symm)
  have apc13 : forall (q18 q19:G), ((q18 ◇ q18) ◇ ((q18 ◇ q18) ◇ q19)) = q19:=by
    intro q18 q19
    exact ((cg (fun t => t ◇ ((q18 ◇ q18) ◇ q19)) (apc1 q18 (q18 ◇ q18) q18)).symm).trans (((cg (fun t => t ◇ ((q18 ◇ q18) ◇ q19)) (cg (fun t => t ◇ ((q18 ◇ q18) ◇ (q18 ◇ q18))) (apc12 (q18 ◇ q18) q18))).symm).trans (apc9 (q18 ◇ q18) q19))
  have apc14 : forall (q20 q21:G), (q21 ◇ (q21 ◇ q20)) = q20:=by
    intro q20 q21
    exact ((((apc13 (q21 ◇ q21) q20).symm).trans (apc12 (((q21 ◇ q21) ◇ (q21 ◇ q21)) ◇ q20) q21)).trans (cg (fun t => q21 ◇ t) (apc12 q20 q21))).symm
  have apc15 : forall (q22 q23:G), ((q23 ◇ q23) ◇ q22) = (q23 ◇ q22):=by
    intro q22 q23
    exact (((cg (fun t => t ◇ q22) (apc13 q23 q23)).symm).trans (apc0 q22 q23 q23)).symm
  have apc16 : forall (q24 q25 q26:G), (q24 ◇ (q26 ◇ q25)) = q25:=by
    intro q24 q25 q26
    exact ((cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q25) (apc14 q26 (q26 ◇ q24)))).symm).trans (((cg (fun t => t ◇ (((q26 ◇ q24) ◇ ((q26 ◇ q24) ◇ q26)) ◇ q25)) (apc14 q24 q26)).symm).trans ((h q25 q26 (q26 ◇ q24)).symm))
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((x ◇ ((y ◇ y) ◇ z)) ◇ x)):=(((cg (fun t => y ◇ t) (cg (fun t => t ◇ x) (cg (fun t => x ◇ t) (apc15 z y)))).trans (cg (fun t => y ◇ t) (cg (fun t => t ◇ x) (apc16 x z y)))).trans (apc16 y x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20301_to_13721 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20301_to_13721
