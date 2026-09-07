-- Equation25454 → Equation36507
-- Recorded verdict: true
-- Premise: x = (y * (z * (y * x))) * (y * z)
-- Conclusion: x = (((y * x) * y) * (x * x)) * x
-- Original submission SHA-256: 38c5bb8de9aee9b367e24cb10bb0de9ae1dfbed8ce30057013480661bed93228
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ (y ◇ x))) ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ x) ◇ y) ◇ (x ◇ x)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q2 ◇ q0))))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q2 ◇ q0))))) (cg (fun t => q2 ◇ t) ((h q0 q2 q1).symm))).symm).trans ((h q1 q2 (q2 ◇ (q1 ◇ (q2 ◇ q0)))).symm)
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ q4) ◇ (q5 ◇ (q5 ◇ q3))) = (q5 ◇ (q4 ◇ (q5 ◇ q3))):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ (q5 ◇ (q5 ◇ q3))) (cg (fun t => q5 ◇ t) (apc0 q3 q4 q5))).symm).trans ((h (q5 ◇ (q4 ◇ (q5 ◇ q3))) q5 (q5 ◇ q3)).symm)
  have apc2 : forall (q6 q7 q8 q9:G), (q7 ◇ ((q8 ◇ q6) ◇ ((q8 ◇ q6) ◇ (q9 ◇ (q8 ◇ (q6 ◇ (q8 ◇ (q7 ◇ (q8 ◇ q6))))))))) = q9:=by
    intro q6 q7 q8 q9
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => (q8 ◇ q6) ◇ t) (cg (fun t => (q8 ◇ q6) ◇ t) (cg (fun t => q9 ◇ t) (apc1 (q7 ◇ (q8 ◇ q6)) q6 q8))))).symm).trans (((cg (fun t => t ◇ ((q8 ◇ q6) ◇ ((q8 ◇ q6) ◇ (q9 ◇ ((q8 ◇ q6) ◇ (q8 ◇ (q8 ◇ (q7 ◇ (q8 ◇ q6))))))))) (apc0 q6 q7 q8)).symm).trans (apc0 (q8 ◇ (q8 ◇ (q7 ◇ (q8 ◇ q6)))) q9 (q8 ◇ q6)))
  have apc3 : forall (q10 q11 q12 q13 q14:G), ((q12 ◇ q11) ◇ (q12 ◇ q10)) = (q12 ◇ (q11 ◇ q10)):=by
    intro q10 q11 q12 q13 q14
    exact (((cg (fun t => (q12 ◇ q11) ◇ t) (cg (fun t => q12 ◇ t) (apc2 q13 q12 q14 q10))).symm).trans (apc1 ((q14 ◇ q13) ◇ ((q14 ◇ q13) ◇ (q10 ◇ (q14 ◇ (q13 ◇ (q14 ◇ (q12 ◇ (q14 ◇ q13)))))))) q11 q12)).trans (cg (fun t => q12 ◇ t) (cg (fun t => q11 ◇ t) (apc2 q13 q12 q14 q10)))
  have apc10 : forall (q0 q15 q16 q17:G), ((q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ ((q17 ◇ q0) ◇ q17)) = (q15 ◇ q16):=by
    intro q0 q15 q16 q17
    exact ((apc3 q17 (q17 ◇ q0) (q15 ◇ (q16 ◇ (q15 ◇ q0))) (((q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ (q17 ◇ q0)) ◇ ((q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ q17)) (((q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ (q17 ◇ q0)) ◇ ((q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ q17))).symm).trans (((cg (fun t => t ◇ ((q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ q17)) (cg (fun t => (q15 ◇ (q16 ◇ (q15 ◇ q0))) ◇ t) (cg (fun t => q17 ◇ t) ((h q0 q15 q16).symm)))).symm).trans ((h (q15 ◇ q16) (q15 ◇ (q16 ◇ (q15 ◇ q0))) q17).symm))
  have apc11 : forall (q18 q19:G), ((q19 ◇ q18) ◇ q19) = q18:=by
    intro q18 q19
    exact ((apc10 q18 (q19 ◇ q18) q19 q19).symm).trans ((h q18 (q19 ◇ q18) q19).symm)
  have apc12 : forall (q20 q21:G), (q20 ◇ (q21 ◇ q20)) = q21:=by
    intro q20 q21
    exact ((cg (fun t => t ◇ (q21 ◇ q20)) (apc11 q20 q21)).symm).trans (apc11 q21 (q21 ◇ q20))
  have apc13 : forall (q22 q23:G), (q22 ◇ q22) = q22:=by
    intro q22 q23
    exact ((((apc12 (q22 ◇ q23) q22).symm).trans (apc3 (q22 ◇ q23) q23 q22 q23 q23)).trans (cg (fun t => q22 ◇ t) (apc12 q23 q22))).symm
  exact (calc
    x = x:=rfl
    _ = ((((y ◇ x) ◇ y) ◇ (x ◇ x)) ◇ x):=((((cg (fun t => t ◇ x) (cg (fun t => ((y ◇ x) ◇ y) ◇ t) (apc13 x (x ◇ x)))).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc11 x y)))).trans (cg (fun t => t ◇ x) (apc13 x (x ◇ x)))).trans (apc13 x (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25454_to_36507 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25454_to_36507
