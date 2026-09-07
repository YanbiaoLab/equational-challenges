-- Equation7067 → Equation179
-- Recorded verdict: true
-- Premise: x = y ◇ (z ◇ ((y ◇ z) ◇ (x ◇ z)))
-- Conclusion: x = (y ◇ y) ◇ (y ◇ x)
-- Original submission SHA-256: cd0a1367dcf14fedbf121468e42e9549f3d84ad5d1bc3fe72f9e42f059d8b46b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((y ◇ z) ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ y) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q1 ◇ ((q3 ◇ q1) ◇ (q0 ◇ q1))) ◇ (q0 ◇ (q2 ◇ (q1 ◇ ((q3 ◇ q1) ◇ (q0 ◇ q1))))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => (q1 ◇ ((q3 ◇ q1) ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => t ◇ (q2 ◇ (q1 ◇ ((q3 ◇ q1) ◇ (q0 ◇ q1))))) ((h q0 q3 q1).symm)))).symm).trans ((h q2 q3 (q1 ◇ ((q3 ◇ q1) ◇ (q0 ◇ q1)))).symm)
  have apc3 : forall (q4 q5 q6:G), (q6 ◇ ((q5 ◇ ((q6 ◇ q5) ◇ (q4 ◇ q5))) ◇ (q4 ◇ q4))) = q6:=by
    intro q4 q5 q6
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => (q5 ◇ ((q6 ◇ q5) ◇ (q4 ◇ q5))) ◇ t) (cg (fun t => q4 ◇ t) ((h q4 q6 q5).symm)))).symm).trans (apc2 q4 q5 q6 q6)
  have apc5 : forall (q7 q8 q9:G), (q8 ◇ (((q9 ◇ (q7 ◇ q7)) ◇ q8) ◇ (q7 ◇ q8))) = (q9 ◇ ((q7 ◇ q7) ◇ (q9 ◇ (q7 ◇ q7)))):=by
    intro q7 q8 q9
    exact (((cg (fun t => q9 ◇ t) (cg (fun t => (q7 ◇ q7) ◇ t) (apc3 q7 q8 (q9 ◇ (q7 ◇ q7))))).symm).trans ((h (q8 ◇ (((q9 ◇ (q7 ◇ q7)) ◇ q8) ◇ (q7 ◇ q8))) q9 (q7 ◇ q7)).symm)).symm
  have apc6 : forall (q10 q11:G), ((q10 ◇ (q11 ◇ q11)) ◇ (q10 ◇ ((q11 ◇ q11) ◇ (q10 ◇ (q11 ◇ q11))))) = q11:=by
    intro q10 q11
    exact ((cg (fun t => (q10 ◇ (q11 ◇ q11)) ◇ t) (apc5 q11 q10 q10)).symm).trans ((h q11 (q10 ◇ (q11 ◇ q11)) q10).symm)
  have apc7 : forall (q12:G), ((q12 ◇ q12) ◇ (q12 ◇ q12)) = (q12 ◇ (q12 ◇ q12)):=by
    intro q12
    exact (((cg (fun t => q12 ◇ t) (apc6 q12 (q12 ◇ q12))).symm).trans (apc2 q12 q12 ((q12 ◇ q12) ◇ (q12 ◇ q12)) q12)).symm
  have apc11 : forall (q13 q14:G), ((q13 ◇ q13) ◇ ((q13 ◇ q13) ◇ ((q13 ◇ (q13 ◇ q13)) ◇ (q14 ◇ (q13 ◇ q13))))) = q14:=by
    intro q13 q14
    exact ((cg (fun t => (q13 ◇ q13) ◇ t) (cg (fun t => (q13 ◇ q13) ◇ t) (cg (fun t => t ◇ (q14 ◇ (q13 ◇ q13))) (apc7 q13)))).symm).trans ((h q14 (q13 ◇ q13) (q13 ◇ q13)).symm)
  have apc12 : forall (q15 q16:G), (q15 ◇ q15) = q15:=by
    intro q15 q16
    exact (((apc3 q16 (q15 ◇ q15) q15).symm).trans (((cg (fun t => q15 ◇ t) (cg (fun t => ((q15 ◇ q15) ◇ ((q15 ◇ (q15 ◇ q15)) ◇ (q16 ◇ (q15 ◇ q15)))) ◇ t) (cg (fun t => q16 ◇ t) (apc11 q15 q16)))).symm).trans (apc2 q16 (q15 ◇ q15) (q15 ◇ q15) q15))).symm
  have apc13 : forall (q16 q15 q10 q11:G), ((q10 ◇ q11) ◇ (q10 ◇ (q11 ◇ (q10 ◇ q11)))) = q11:=by
    intro q16 q15 q10 q11
    exact ((((cg (fun t => (q10 ◇ (q11 ◇ q11)) ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => (q11 ◇ q11) ◇ t) (cg (fun t => q10 ◇ t) (apc12 q11 (q11 ◇ q11)))))).trans (cg (fun t => (q10 ◇ (q11 ◇ q11)) ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ (q10 ◇ q11)) (apc12 q11 (q11 ◇ q11)))))).trans (cg (fun t => t ◇ (q10 ◇ (q11 ◇ (q10 ◇ q11)))) (cg (fun t => q10 ◇ t) (apc12 q11 (q11 ◇ q11))))).symm).trans (apc6 q10 q11)
  have apc14 : forall (q17 q18:G), (q17 ◇ (q18 ◇ (q17 ◇ q18))) = q17:=by
    intro q17 q18
    exact ((cg (fun t => q17 ◇ t) (cg (fun t => q18 ◇ t) (apc12 (q17 ◇ q18) q17))).symm).trans ((h q17 q17 q18).symm)
  have apc15 : forall (q16 q15 q17 q18 q10 q11:G), ((q10 ◇ q11) ◇ q10) = q11:=by
    intro q16 q15 q17 q18 q10 q11
    exact ((cg (fun t => (q10 ◇ q11) ◇ t) (apc14 q10 q11)).symm).trans (apc13 q16 q15 q10 q11)
  have apc16 : forall (q19 q20:G), ((q19 ◇ q20) ◇ q20) = q19:=by
    intro q19 q20
    exact ((cg (fun t => (q19 ◇ q20) ◇ t) (apc12 q20 (q20 ◇ q20))).symm).trans (((cg (fun t => (q19 ◇ q20) ◇ t) (cg (fun t => q20 ◇ t) (apc15 q19 q19 q19 q19 (q19 ◇ q20) q20))).symm).trans ((h q19 (q19 ◇ q20) q20).symm))
  have apc17 : forall (q21 q22:G), (q21 ◇ (q21 ◇ q22)) = q22:=by
    intro q21 q22
    exact ((cg (fun t => t ◇ (q21 ◇ q22)) (apc16 q21 q22)).symm).trans (apc15 q21 q21 q21 q21 (q21 ◇ q22) q22)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ y) ◇ (y ◇ x)):=((cg (fun t => t ◇ (y ◇ x)) (apc12 y (y ◇ y))).trans (apc17 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7067_to_179 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_7067_to_179
