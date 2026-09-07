-- Equation9740 → Equation56446
-- Recorded verdict: true
-- Premise: x = y ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y)))
-- Conclusion: x ◇ (x ◇ x) = (x ◇ (y ◇ y)) ◇ x
-- Original submission SHA-256: 40d045f4a33a86e98210636058da46d337634db0e22fa81d2d8a23889191fc7d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = (x ◇ (y ◇ y)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q1 ◇ q1)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q1 ◇ q1)) ◇ t) ((h (q0 ◇ q0) (q1 ◇ q1) q0).symm)).symm).trans ((h (q0 ◇ q0) ((q0 ◇ q0) ◇ (q1 ◇ q1)) q1).symm)
  have apc2 : forall (q2 q3 q4:G), ((q2 ◇ q2) ◇ ((q4 ◇ q4) ◇ (q2 ◇ q2))) = ((q2 ◇ q2) ◇ (q3 ◇ q3)):=by
    intro q2 q3 q4
    exact ((cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => (q4 ◇ q4) ◇ t) (apc0 q2 q3))).symm).trans (((cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => (q4 ◇ q4) ◇ t) (cg (fun t => ((q2 ◇ q2) ◇ (q3 ◇ q3)) ◇ t) (apc0 q2 q3)))).symm).trans ((h ((q2 ◇ q2) ◇ (q3 ◇ q3)) (q2 ◇ q2) q4).symm))
  have apc3 : forall (q2 q3 q4:G), ((q2 ◇ q2) ◇ (q3 ◇ q3)) = ((q2 ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q2 q3 q4
    exact ((apc2 q2 q3 q4).symm).trans (apc2 q2 q2 q4)
  have apc4 : forall (q5 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q5 q6
    exact (((cg (fun t => (q5 ◇ q5) ◇ t) (apc3 q6 (q5 ◇ q5) ((q6 ◇ q6) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5))))).trans (apc3 q5 (q6 ◇ q6) ((q5 ◇ q5) ◇ ((q6 ◇ q6) ◇ (q6 ◇ q6))))).symm).trans (((cg (fun t => (q5 ◇ q5) ◇ t) (cg (fun t => (q6 ◇ q6) ◇ t) (apc3 q5 (q5 ◇ q5) q5))).symm).trans ((h (q5 ◇ q5) (q5 ◇ q5) q6).symm))
  have apc5 : forall (x y z:G), (y ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y)))) = (x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc8 : forall (q2 q3 q4:G), ((q2 ◇ q2) ◇ (q3 ◇ q3)) = (q2 ◇ q2):=by
    intro q2 q3 q4
    exact (apc3 q2 q3 q4).trans (apc4 q2 ((q2 ◇ q2) ◇ (q2 ◇ q2)))
  have apc10 : forall (q7:G), (q7 ◇ ((q7 ◇ q7) ◇ (q7 ◇ (q7 ◇ q7)))) = q7:=by
    intro q7
    exact ((apc5 q7 q7 q7).symm).trans ((h q7 q7 q7).symm)
  have apc11 : forall (q8 q0 q9 q1:G), (((q0 ◇ q0) ◇ (q8 ◇ (q8 ◇ q9))) ◇ ((q1 ◇ q1) ◇ (q9 ◇ q8))) = q9:=by
    intro q8 q0 q9 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q8 ◇ (q8 ◇ q9))) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q9 ◇ t) ((h q8 q9 q0).symm)))).symm).trans ((h q9 ((q0 ◇ q0) ◇ (q8 ◇ (q8 ◇ q9))) q1).symm)
  have apc12 : forall (q10 q11:G), (((q10 ◇ q10) ◇ (q10 ◇ (q10 ◇ q10))) ◇ (q11 ◇ q11)) = q10:=by
    intro q10 q11
    exact ((cg (fun t => ((q10 ◇ q10) ◇ (q10 ◇ (q10 ◇ q10))) ◇ t) (apc8 q11 q10 ((q11 ◇ q11) ◇ (q10 ◇ q10)))).symm).trans (((cg (fun t => ((q10 ◇ q10) ◇ (q10 ◇ (q10 ◇ q10))) ◇ t) (cg (fun t => (q11 ◇ q11) ◇ t) (cg (fun t => q10 ◇ t) (apc10 q10)))).symm).trans ((h q10 ((q10 ◇ q10) ◇ (q10 ◇ (q10 ◇ q10))) q11).symm))
  have apc13 : forall (q12 q13 q14:G), ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))) = (((q13 ◇ q13) ◇ q12) ◇ (q14 ◇ q14)):=by
    intro q12 q13 q14
    exact (((cg (fun t => ((q13 ◇ q13) ◇ q12) ◇ t) (apc8 q14 ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))) ((q14 ◇ q14) ◇ (((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))) ◇ ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))))))).symm).trans (((cg (fun t => t ◇ ((q14 ◇ q14) ◇ (((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))) ◇ ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12)))))) (cg (fun t => (q13 ◇ q13) ◇ t) (apc12 q12 ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12)))))).symm).trans (apc11 ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))) q13 ((q12 ◇ q12) ◇ (q12 ◇ (q12 ◇ q12))) q14))).symm
  have apc17 : forall (q15 q16 q17:G), (q17 ◇ (((q15 ◇ q15) ◇ q17) ◇ (q16 ◇ q16))) = q17:=by
    intro q15 q16 q17
    exact ((cg (fun t => q17 ◇ t) (apc13 q17 q15 q16)).symm).trans ((h q17 q17 q17).symm)
  have apc18 : forall (q18:G), ((q18 ◇ (q18 ◇ q18)) ◇ q18) = (q18 ◇ (q18 ◇ q18)):=by
    intro q18
    exact ((cg (fun t => (q18 ◇ (q18 ◇ q18)) ◇ t) (apc11 q18 q18 q18 q18)).symm).trans (apc17 q18 (q18 ◇ q18) (q18 ◇ (q18 ◇ q18)))
  have apc19 : forall (q19 q20:G), (q19 ◇ (q20 ◇ q20)) = (q19 ◇ (q19 ◇ q19)):=by
    intro q19 q20
    exact ((cg (fun t => q19 ◇ t) (apc8 q20 (q19 ◇ (q19 ◇ q19)) ((q20 ◇ q20) ◇ ((q19 ◇ (q19 ◇ q19)) ◇ (q19 ◇ (q19 ◇ q19)))))).symm).trans (((cg (fun t => q19 ◇ t) (cg (fun t => (q20 ◇ q20) ◇ t) (cg (fun t => (q19 ◇ (q19 ◇ q19)) ◇ t) (apc18 q19)))).symm).trans ((h (q19 ◇ (q19 ◇ q19)) q19 q20).symm))
  exact (calc
    (x ◇ (x ◇ x)) = (x ◇ (x ◇ x)):=rfl
    _ = ((x ◇ (y ◇ y)) ◇ x):=((cg (fun t => t ◇ x) (apc19 x y)).trans (apc18 x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9740_to_56446 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_9740_to_56446
