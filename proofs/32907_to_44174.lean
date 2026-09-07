-- Equation32907 → Equation44174
-- Recorded verdict: true
-- Premise: x = (x ◇ (((y ◇ z) ◇ y) ◇ y)) ◇ y
-- Conclusion: x ◇ x = x ◇ ((x ◇ (y ◇ z)) ◇ w)
-- Original submission SHA-256: 9cce4b3662e21aaa58e0494eeedd8987e4dd89398d9b1ef0e6f8aa0f84631be7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (((y ◇ z) ◇ y) ◇ y)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = x ◇ ((x ◇ (y ◇ z)) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ (q1 ◇ q1)) ◇ q1) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q1) ((h q1 q1 q0).symm)))).symm).trans ((h q0 q1 (((q1 ◇ q0) ◇ q1) ◇ q1)).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) = (q2 ◇ q3):=by
    intro q2 q3
    exact (((cg (fun t => t ◇ q3) (apc0 q2 (q3 ◇ q3))).symm).trans (apc0 (q2 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) q3)).symm
  have apc2 : forall (q4 q5:G), ((q5 ◇ q4) ◇ (q4 ◇ q4)) = q5:=by
    intro q4 q5
    exact ((cg (fun t => t ◇ (q4 ◇ q4)) (apc1 q5 q4)).symm).trans (apc0 q5 (q4 ◇ q4))
  have apc4 : forall (q6 q7 q8:G), (q6 ◇ (((q8 ◇ q7) ◇ q8) ◇ q8)) = (q6 ◇ (q8 ◇ q8)):=by
    intro q6 q7 q8
    exact (((cg (fun t => t ◇ (q8 ◇ q8)) ((h q6 q8 q7).symm)).symm).trans (apc2 q8 (q6 ◇ (((q8 ◇ q7) ◇ q8) ◇ q8)))).symm
  have apc5 : forall (q9 q10 q11:G), (q11 ◇ ((q10 ◇ (q10 ◇ q9)) ◇ (q10 ◇ q9))) = (q11 ◇ ((q10 ◇ q9) ◇ (q10 ◇ q9))):=by
    intro q9 q10 q11
    exact ((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ (q10 ◇ q9)) (cg (fun t => t ◇ (q10 ◇ q9)) (apc2 q9 q10)))).symm).trans (apc4 q11 (q9 ◇ q9) (q10 ◇ q9))
  have apc6 : forall (q12 q13 q14:G), (q14 ◇ ((q13 ◇ q12) ◇ (q13 ◇ q13))) = (q14 ◇ ((q13 ◇ q12) ◇ q13)):=by
    intro q12 q13 q14
    exact (((cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (q13 ◇ q13)) (apc4 ((q13 ◇ q12) ◇ q13) q12 q13))).trans (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (q13 ◇ q13)) (apc2 q13 (q13 ◇ q12))))).symm).trans ((((cg (fun t => q14 ◇ t) (apc4 (((q13 ◇ q12) ◇ q13) ◇ (((q13 ◇ q12) ◇ q13) ◇ q13)) q12 q13)).symm).trans (apc5 q13 ((q13 ◇ q12) ◇ q13) q14)).trans ((cg (fun t => q14 ◇ t) (apc4 (((q13 ◇ q12) ◇ q13) ◇ q13) q12 q13)).trans (cg (fun t => q14 ◇ t) (apc2 q13 ((q13 ◇ q12) ◇ q13)))))
  have apc7 : forall (q15 q16:G), (q16 ◇ ((q15 ◇ q15) ◇ q15)) = (q16 ◇ q15):=by
    intro q15 q16
    exact (((cg (fun t => q16 ◇ t) (apc2 q15 q15)).symm).trans (apc6 q15 q15 q16)).symm
  have apc9 : forall (q17 q18 q19:G), (q19 ◇ (q18 ◇ q18)) = (q19 ◇ (q18 ◇ q17)):=by
    intro q17 q18 q19
    exact (((((cg (fun t => q19 ◇ t) (cg (fun t => t ◇ (q18 ◇ q18)) (apc4 (((q18 ◇ q17) ◇ q18) ◇ q18) q17 q18))).trans (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ (q18 ◇ q18)) (apc2 q18 ((q18 ◇ q17) ◇ q18))))).trans (cg (fun t => q19 ◇ t) (apc2 q18 (q18 ◇ q17)))).symm).trans ((((cg (fun t => q19 ◇ t) (apc4 ((((q18 ◇ q17) ◇ q18) ◇ q18) ◇ (((q18 ◇ q17) ◇ q18) ◇ q18)) q17 q18)).symm).trans (apc7 (((q18 ◇ q17) ◇ q18) ◇ q18) q19)).trans (apc4 q19 q17 q18))).symm
  have apc10 : forall (q20 q21 q22 q23:G), (q23 ◇ (q22 ◇ q21)) = (q23 ◇ (q22 ◇ q20)):=by
    intro q20 q21 q22 q23
    exact (((apc9 q20 q22 q23).symm).trans (apc9 q21 q22 q23)).symm
  have apc17 : forall (q24 q25 q26 q27:G), (q27 ◇ ((q25 ◇ q24) ◇ q26)) = (q27 ◇ q25):=by
    intro q24 q25 q26 q27
    exact (((cg (fun t => q27 ◇ t) (apc2 q24 q25)).symm).trans (apc10 q26 (q24 ◇ q24) (q25 ◇ q24) q27)).symm
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = (x ◇ ((x ◇ (y ◇ z)) ◇ w)):=(apc17 (y ◇ z) x w x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32907_to_44174 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32907_to_44174
