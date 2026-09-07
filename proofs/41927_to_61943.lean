-- Equation41927 → Equation61943
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (y ◇ (x ◇ (z ◇ y)))
-- Conclusion: (x ◇ y) ◇ x = ((y ◇ x) ◇ y) ◇ x
-- Original submission SHA-256: e79244a842252b612bee17923c1d647a2e6378fa0ec1dd7192341f686cc0d46b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ (x ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ x = ((y ◇ x) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (y ◇ (x ◇ (z ◇ y)))) = (y ◇ (y ◇ (x ◇ (x ◇ y)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), (y ◇ (y ◇ (x ◇ (x ◇ y)))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2:G), ((q0 ◇ (q1 ◇ q2)) ◇ ((q0 ◇ (q1 ◇ q2)) ◇ (q0 ◇ q2))) = (q2 ◇ (q0 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q0 ◇ (q1 ◇ q2)) ◇ t) (cg (fun t => (q0 ◇ (q1 ◇ q2)) ◇ t) ((h q0 q2 q1).symm))).symm).trans ((h q2 (q0 ◇ (q1 ◇ q2)) q2).symm)
  have apc4 : forall (q3 q4:G), ((q3 ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) = ((q3 ◇ q4) ◇ ((q3 ◇ q4) ◇ (q4 ◇ (q3 ◇ (q3 ◇ q4))))):=by
    intro q3 q4
    exact (((cg (fun t => (q3 ◇ q4) ◇ t) (cg (fun t => t ◇ (q4 ◇ (q3 ◇ (q3 ◇ q4)))) (apc1 q3 q4 (q4 ◇ (q4 ◇ (q3 ◇ (q3 ◇ q4))))))).symm).trans ((((cg (fun t => t ◇ ((q4 ◇ (q4 ◇ (q3 ◇ (q3 ◇ q4)))) ◇ (q4 ◇ (q3 ◇ (q3 ◇ q4))))) (apc1 q3 q4 q3)).symm).trans (apc2 q4 q4 (q3 ◇ (q3 ◇ q4)))).trans (cg (fun t => (q3 ◇ (q3 ◇ q4)) ◇ t) (apc1 q3 q4 (q4 ◇ (q4 ◇ (q3 ◇ (q3 ◇ q4)))))))).symm
  have apc7 : forall (q5 q6:G), ((q5 ◇ q6) ◇ (q6 ◇ (q5 ◇ (q5 ◇ q6)))) = (q5 ◇ q6):=by
    intro q5 q6
    exact ((apc2 q6 q5 (q5 ◇ q6)).symm).trans ((((cg (fun t => (q6 ◇ (q5 ◇ (q5 ◇ q6))) ◇ t) (cg (fun t => (q6 ◇ (q5 ◇ (q5 ◇ q6))) ◇ t) (cg (fun t => q6 ◇ t) (apc1 q5 q6 q5)))).symm).trans (apc1 q6 (q6 ◇ (q5 ◇ (q5 ◇ q6))) q5)).trans (apc1 q5 q6 (q6 ◇ (q6 ◇ (q5 ◇ (q5 ◇ q6))))))
  have apc8 : forall (q7 q8:G), ((q8 ◇ q7) ◇ (q8 ◇ q7)) = (q7 ◇ (q8 ◇ q7)):=by
    intro q7 q8
    exact ((cg (fun t => (q8 ◇ q7) ◇ t) (apc7 q8 q7)).symm).trans ((h q7 (q8 ◇ q7) q8).symm)
  have apc11 : forall (q5 q6 q3 q4:G), ((q3 ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) = (q4 ◇ (q3 ◇ q4)):=by
    intro q5 q6 q3 q4
    exact ((apc4 q3 q4).trans (cg (fun t => (q3 ◇ q4) ◇ t) (apc7 q3 q4))).trans (apc8 q4 q3)
  have apc12 : forall (q9 q8:G), ((q9 ◇ (q9 ◇ q8)) ◇ (q8 ◇ (q9 ◇ q8))) = ((q9 ◇ q8) ◇ (q9 ◇ (q9 ◇ q8))):=by
    intro q9 q8
    exact ((cg (fun t => (q9 ◇ (q9 ◇ q8)) ◇ t) (apc11 ((q9 ◇ (q9 ◇ q8)) ◇ (q9 ◇ q8)) ((q9 ◇ (q9 ◇ q8)) ◇ (q9 ◇ q8)) q9 q8)).symm).trans (((cg (fun t => (q9 ◇ (q9 ◇ q8)) ◇ t) (cg (fun t => (q9 ◇ (q9 ◇ q8)) ◇ t) (apc7 q9 q8))).symm).trans ((h (q9 ◇ q8) (q9 ◇ (q9 ◇ q8)) q8).symm))
  have apc23 : forall (q10 q11:G), ((q10 ◇ q11) ◇ (q10 ◇ (q10 ◇ q11))) = (q11 ◇ (q10 ◇ (q10 ◇ q11))):=by
    intro q10 q11
    exact ((apc12 q10 q11).symm).trans (((cg (fun t => (q10 ◇ (q10 ◇ q11)) ◇ t) (apc11 q10 q10 q10 q11)).symm).trans (apc2 q10 q10 q11))
  have apc27 : forall (q12 q13:G), ((q12 ◇ (q12 ◇ q13)) ◇ (q13 ◇ (q12 ◇ (q12 ◇ q13)))) = (q12 ◇ q13):=by
    intro q12 q13
    exact (((apc7 q12 q13).symm).trans (((cg (fun t => t ◇ (q13 ◇ (q12 ◇ (q12 ◇ q13)))) (apc1 q12 q13 q12)).symm).trans (apc11 q12 q12 q13 (q12 ◇ (q12 ◇ q13))))).symm
  have apc28 : forall (q14 q15:G), ((q14 ◇ q15) ◇ (q15 ◇ (q14 ◇ q15))) = (q15 ◇ (q14 ◇ (q14 ◇ q15))):=by
    intro q14 q15
    exact (((cg (fun t => (q14 ◇ q15) ◇ t) (cg (fun t => (q14 ◇ (q14 ◇ q15)) ◇ t) (apc1 q14 q15 (q15 ◇ (q15 ◇ (q14 ◇ (q14 ◇ q15))))))).trans (cg (fun t => (q14 ◇ q15) ◇ t) (apc11 ((q14 ◇ (q14 ◇ q15)) ◇ (q14 ◇ q15)) ((q14 ◇ (q14 ◇ q15)) ◇ (q14 ◇ q15)) q14 q15))).symm).trans (((cg (fun t => t ◇ ((q14 ◇ (q14 ◇ q15)) ◇ (q15 ◇ (q15 ◇ (q14 ◇ (q14 ◇ q15)))))) (apc1 q14 q15 q14)).symm).trans (apc27 q15 (q14 ◇ (q14 ◇ q15))))
  have apc29 : forall (q16 q17:G), ((q17 ◇ q16) ◇ (q17 ◇ (q17 ◇ (q17 ◇ q16)))) = (q17 ◇ q16):=by
    intro q16 q17
    exact (((apc27 q17 q16).symm).trans (((cg (fun t => (q17 ◇ (q17 ◇ q16)) ◇ t) (apc23 q17 q16)).symm).trans (apc28 q17 (q17 ◇ q16)))).symm
  have apc30 : forall (q18 q19:G), (q19 ◇ (q19 ◇ q18)) = (q18 ◇ (q19 ◇ q18)):=by
    intro q18 q19
    exact (((apc8 q18 q19).symm).trans (((cg (fun t => (q19 ◇ q18) ◇ t) (apc29 q18 q19)).symm).trans ((h q19 (q19 ◇ q18) q19).symm))).symm
  have apc33 : forall (q20 q21:G), (q20 ◇ (q20 ◇ (q20 ◇ (q21 ◇ q20)))) = (q20 ◇ q20):=by
    intro q20 q21
    exact (((cg (fun t => q20 ◇ t) (apc28 q21 q20)).trans (cg (fun t => q20 ◇ t) (cg (fun t => q20 ◇ t) (apc30 q20 q21)))).symm).trans (((cg (fun t => q20 ◇ t) (apc30 (q21 ◇ q20) q20)).symm).trans ((h q20 q20 q21).symm))
  have apc41 : forall (q22 q21:G), (q21 ◇ q22) = (q22 ◇ q22):=by
    intro q22 q21
    exact (((apc33 q22 q21).symm).trans (((cg (fun t => q22 ◇ t) (cg (fun t => q22 ◇ t) (apc30 q22 q21))).symm).trans ((h q21 q22 q21).symm))).symm
  exact (apc41 x (x ◇ y)).trans ((apc41 x ((y ◇ x) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41927_to_61943 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41927_to_61943
