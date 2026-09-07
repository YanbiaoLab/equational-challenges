-- Equation30498 → Equation532
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ ((x ◇ y) ◇ z))) ◇ x
-- Conclusion: x = y ◇ (y ◇ (z ◇ (w ◇ x)))
-- Original submission SHA-256: 4c8de7a2fe8b6682894d4a5ad3f848cb7665c10ea84842ff09186c5b5aed7430
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ ((x ◇ y) ◇ z))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (y ◇ (z ◇ (w ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (y ◇ ((x ◇ y) ◇ z))) ◇ x) = ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2:G), (((q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ ((q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ q2)) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ ((q2 ◇ q1) ◇ q0)) ◇ t) ((h q2 q1 q0).symm)))).symm).trans ((h q1 (q1 ◇ ((q2 ◇ q1) ◇ q0)) q2).symm)
  have apc3 : forall (q3 q0 q4 q2:G), ((q4 ◇ (q4 ◇ (q4 ◇ q2))) ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q0)))) = (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q0))):=by
    intro q3 q0 q4 q2
    exact ((cg (fun t => t ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q0)))) (cg (fun t => q4 ◇ t) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q2) ((h q4 q3 q0).symm))))).symm).trans ((h (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q0))) q4 q2).symm)
  have apc5 : forall (q5 q6 q7:G), (q7 ◇ (q5 ◇ (q5 ◇ (((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q5) ◇ q6)))) = (q5 ◇ (q5 ◇ (((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q5) ◇ q6))):=by
    intro q5 q6 q7
    exact (((cg (fun t => t ◇ (q5 ◇ (q5 ◇ (((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q5) ◇ q6)))) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (apc1 q7 ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q7) ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q7)))).trans (cg (fun t => t ◇ (q5 ◇ (q5 ◇ (((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q5) ◇ q6)))) (apc1 q7 ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q7) ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q7)))).symm).trans (((cg (fun t => t ◇ (q5 ◇ (q5 ◇ (((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q5) ◇ q6)))) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (apc1 q7 q5 q5)))).symm).trans (apc3 q5 q6 (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) q7))
  have apc6 : forall (q8 q9:G), (q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q9)))) = (q8 ◇ (q8 ◇ (q8 ◇ q9))):=by
    intro q8 q9
    exact (((cg (fun t => q8 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q9) ((h q8 q8 q8).symm))))).symm).trans (apc5 q8 q9 q8)).trans (cg (fun t => q8 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q9) (apc1 q8 ((q8 ◇ (q8 ◇ ((q8 ◇ q8) ◇ q8))) ◇ q8) ((q8 ◇ (q8 ◇ ((q8 ◇ q8) ◇ q8))) ◇ q8)))))
  have apc8 : forall (q10 q11 q12:G), (((q11 ◇ q12) ◇ ((q11 ◇ q12) ◇ (((q12 ◇ (q12 ◇ ((q12 ◇ q12) ◇ q12))) ◇ (q11 ◇ q12)) ◇ q10))) ◇ q11) = q11:=by
    intro q10 q11 q12
    exact ((cg (fun t => t ◇ q11) (apc5 (q11 ◇ q12) q10 q12)).symm).trans (((cg (fun t => t ◇ q11) (cg (fun t => q12 ◇ t) (apc5 (q11 ◇ q12) q10 q12))).symm).trans ((h q11 q12 ((q11 ◇ q12) ◇ (((q12 ◇ (q12 ◇ ((q12 ◇ q12) ◇ q12))) ◇ (q11 ◇ q12)) ◇ q10))).symm))
  have apc11 : forall (q13 q14 q15:G), (((q14 ◇ (q14 ◇ (q14 ◇ q13))) ◇ ((q14 ◇ (q14 ◇ (q14 ◇ q13))) ◇ ((q14 ◇ (q14 ◇ (q14 ◇ q13))) ◇ q15))) ◇ q14) = q14:=by
    intro q13 q14 q15
    exact ((cg (fun t => t ◇ q14) (cg (fun t => (q14 ◇ (q14 ◇ (q14 ◇ q13))) ◇ t) (cg (fun t => (q14 ◇ (q14 ◇ (q14 ◇ q13))) ◇ t) (cg (fun t => t ◇ q15) (apc6 q14 q13))))).symm).trans ((h q14 (q14 ◇ (q14 ◇ (q14 ◇ q13))) q15).symm)
  have apc13 : forall (q16 q17 q18 q19:G), ((q18 ◇ (q18 ◇ (q18 ◇ q19))) ◇ ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ q17))) = ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ q17)):=by
    intro q16 q17 q18 q19
    exact ((cg (fun t => t ◇ ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ q17))) (cg (fun t => q18 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => t ◇ q19) (apc2 q16 q18 q17))))).symm).trans ((h ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ ((q18 ◇ ((q17 ◇ q18) ◇ q16)) ◇ q17)) q18 q19).symm)
  have apc14 : forall (q20 q21 q22:G), ((q21 ◇ (q21 ◇ (q21 ◇ q22))) ◇ q20) = q20:=by
    intro q20 q21 q22
    exact ((((cg (fun t => (q21 ◇ (q21 ◇ (q21 ◇ q22))) ◇ t) (cg (fun t => ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ (q20 ◇ q21)) ◇ q20))) ◇ t) (cg (fun t => t ◇ q20) (apc5 (q20 ◇ q21) q20 q21)))).trans (cg (fun t => (q21 ◇ (q21 ◇ (q21 ◇ q22))) ◇ t) (cg (fun t => ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ (q20 ◇ q21)) ◇ q20))) ◇ t) (apc8 q20 q20 q21)))).trans (cg (fun t => (q21 ◇ (q21 ◇ (q21 ◇ q22))) ◇ t) (apc8 q20 q20 q21))).symm).trans ((((cg (fun t => (q21 ◇ (q21 ◇ (q21 ◇ q22))) ◇ t) (cg (fun t => t ◇ ((q21 ◇ ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ (q20 ◇ q21)) ◇ q20)))) ◇ q20)) (apc5 (q20 ◇ q21) q20 q21))).symm).trans (apc13 ((q20 ◇ q21) ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ (q20 ◇ q21)) ◇ q20)) q20 q21 q22)).trans ((((cg (fun t => (q21 ◇ ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ (q20 ◇ q21)) ◇ q20)))) ◇ t) (cg (fun t => t ◇ q20) (apc5 (q20 ◇ q21) q20 q21))).trans (cg (fun t => (q21 ◇ ((q20 ◇ q21) ◇ ((q20 ◇ q21) ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ (q20 ◇ q21)) ◇ q20)))) ◇ t) (apc8 q20 q20 q21))).trans (cg (fun t => t ◇ q20) (apc5 (q20 ◇ q21) q20 q21))).trans (apc8 q20 q20 q21)))
  have apc15 : forall (q20 q21 q22 q13 q14 q15:G), (q15 ◇ q14) = q14:=by
    intro q20 q21 q22 q13 q14 q15
    exact ((((cg (fun t => t ◇ q14) (cg (fun t => (q14 ◇ (q14 ◇ (q14 ◇ q14))) ◇ t) (cg (fun t => (q14 ◇ (q14 ◇ (q14 ◇ q14))) ◇ t) (apc14 q15 q14 q14)))).trans (cg (fun t => t ◇ q14) (cg (fun t => (q14 ◇ (q14 ◇ (q14 ◇ q14))) ◇ t) (apc14 q15 q14 q14)))).trans (cg (fun t => t ◇ q14) (apc14 q15 q14 q14))).symm).trans (apc11 q14 q14 q15)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (y ◇ (z ◇ (w ◇ x)))):=((((cg (fun t => y ◇ t) (cg (fun t => y ◇ t) (cg (fun t => z ◇ t) (apc15 (w ◇ x) (w ◇ x) (w ◇ x) (w ◇ x) x w)))).trans (cg (fun t => y ◇ t) (cg (fun t => y ◇ t) (apc15 (z ◇ x) (z ◇ x) (z ◇ x) (z ◇ x) x z)))).trans (cg (fun t => y ◇ t) (apc15 (y ◇ x) (y ◇ x) (y ◇ x) (y ◇ x) x y))).trans (apc15 (y ◇ x) (y ◇ x) (y ◇ x) (y ◇ x) x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30498_to_532 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30498_to_532
