-- Equation29497 → Equation2249
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ (y ◇ (x ◇ z)))) ◇ x
-- Conclusion: x = (x ◇ (x ◇ (y ◇ z))) ◇ x
-- Original submission SHA-256: b8f0650714f08c56d6b34be90de7cebca9f2c3ffcc1638ed2f5c2f51e47ade39
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (y ◇ (x ◇ z)))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ z))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (x ◇ (y ◇ (x ◇ z)))) ◇ x) = ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (((q0 ◇ ((q2 ◇ q3) ◇ (q0 ◇ ((q2 ◇ q3) ◇ q1)))) ◇ (q2 ◇ (q2 ◇ q3))) ◇ q2) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q2) (cg (fun t => (q0 ◇ ((q2 ◇ q3) ◇ (q0 ◇ ((q2 ◇ q3) ◇ q1)))) ◇ t) (cg (fun t => q2 ◇ t) ((h (q2 ◇ q3) q0 q1).symm)))).symm).trans ((h q2 (q0 ◇ ((q2 ◇ q3) ◇ (q0 ◇ ((q2 ◇ q3) ◇ q1)))) q3).symm)
  have apc3 : forall (q4 q5 q6:G), (((q4 ◇ (q6 ◇ (q4 ◇ (q6 ◇ q5)))) ◇ q6) ◇ (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6))))) = (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))):=by
    intro q4 q5 q6
    exact ((((cg (fun t => t ◇ (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6))))) (cg (fun t => t ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) (cg (fun t => q4 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q5) (apc1 q6 ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6) ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6)))))))).trans (cg (fun t => t ◇ (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6))))) (cg (fun t => (q4 ◇ (q6 ◇ (q4 ◇ (q6 ◇ q5)))) ◇ t) (cg (fun t => (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ t) (apc1 q6 ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6) ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6)))))).trans (cg (fun t => t ◇ (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6))))) (cg (fun t => (q4 ◇ (q6 ◇ (q4 ◇ (q6 ◇ q5)))) ◇ t) (apc1 q6 ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6) ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))))).symm).trans (((cg (fun t => t ◇ (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6))))) (cg (fun t => t ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ ((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6))) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q4 ◇ (((q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) ◇ q6) ◇ q5))) (apc1 q6 q4 q4))))).symm).trans (apc2 q4 q5 (q6 ◇ (q6 ◇ (q6 ◇ (q6 ◇ q6)))) q6))
  have apc4 : forall (q7:G), (q7 ◇ (q7 ◇ (q7 ◇ (q7 ◇ (q7 ◇ q7))))) = (q7 ◇ (q7 ◇ (q7 ◇ (q7 ◇ q7)))):=by
    intro q7
    exact ((cg (fun t => t ◇ (q7 ◇ (q7 ◇ (q7 ◇ (q7 ◇ q7))))) ((h q7 q7 q7).symm)).symm).trans (apc3 q7 q7 q7)
  have apc5 : forall (q8 q9:G), ((q9 ◇ (q8 ◇ (q9 ◇ (q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8))))))) ◇ q8) = q8:=by
    intro q8 q9
    exact ((cg (fun t => t ◇ q8) (cg (fun t => q9 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => q9 ◇ t) (apc4 q8))))).symm).trans ((h q8 q9 (q8 ◇ (q8 ◇ (q8 ◇ (q8 ◇ q8))))).symm)
  have apc8 : forall (q10 q11 q12 q13:G), (((q11 ◇ (q13 ◇ (q11 ◇ (q13 ◇ q12)))) ◇ q13) ◇ (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13)))))))) = (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))):=by
    intro q10 q11 q12 q13
    exact ((((cg (fun t => t ◇ (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13)))))))) (cg (fun t => t ◇ ((q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) ◇ ((q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) ◇ q13))) (cg (fun t => q11 ◇ t) (cg (fun t => q13 ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q12) (apc5 q13 q10))))))).trans (cg (fun t => t ◇ (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13)))))))) (cg (fun t => (q11 ◇ (q13 ◇ (q11 ◇ (q13 ◇ q12)))) ◇ t) (cg (fun t => (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) ◇ t) (apc5 q13 q10))))).trans (cg (fun t => t ◇ (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13)))))))) (cg (fun t => (q11 ◇ (q13 ◇ (q11 ◇ (q13 ◇ q12)))) ◇ t) (apc5 q13 q10)))).symm).trans (((cg (fun t => t ◇ (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13)))))))) (cg (fun t => t ◇ ((q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) ◇ ((q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) ◇ q13))) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ (q11 ◇ (((q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) ◇ q13) ◇ q12))) (apc5 q13 q10))))).symm).trans (apc2 q11 q12 (q10 ◇ (q13 ◇ (q10 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q13))))))) q13))
  have apc9 : forall (q14 q15:G), (q15 ◇ (q14 ◇ (q15 ◇ (q14 ◇ (q15 ◇ (q15 ◇ (q15 ◇ (q15 ◇ q15)))))))) = (q14 ◇ (q15 ◇ (q14 ◇ (q15 ◇ (q15 ◇ (q15 ◇ (q15 ◇ q15))))))):=by
    intro q14 q15
    exact ((cg (fun t => t ◇ (q14 ◇ (q15 ◇ (q14 ◇ (q15 ◇ (q15 ◇ (q15 ◇ (q15 ◇ q15)))))))) ((h q15 q14 q14).symm)).symm).trans (apc8 q14 q14 q14 q15)
  have apc10 : forall (q16 q17:G), ((q16 ◇ (q17 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q17 ◇ (q17 ◇ q17))))))) ◇ q16) = q16:=by
    intro q16 q17
    exact ((cg (fun t => t ◇ q16) (apc9 q16 q17)).symm).trans ((h q16 q17 (q17 ◇ (q17 ◇ (q17 ◇ (q17 ◇ q17))))).symm)
  have apc11 : forall (q18 q19:G), ((q18 ◇ (q18 ◇ q19)) ◇ q18) = q18:=by
    intro q18 q19
    exact ((cg (fun t => t ◇ q18) (apc10 (q18 ◇ (q18 ◇ q19)) (q18 ◇ q19))).symm).trans (apc2 (q18 ◇ (q18 ◇ q19)) ((q18 ◇ q19) ◇ ((q18 ◇ q19) ◇ ((q18 ◇ q19) ◇ (q18 ◇ q19)))) q18 q19)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (x ◇ (y ◇ z))) ◇ x):=(apc11 x (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29497_to_2249 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29497_to_2249
