-- Equation33015 → Equation53946
-- Recorded verdict: true
-- Premise: x = (y ◇ (((x ◇ y) ◇ y) ◇ z)) ◇ x
-- Conclusion: x ◇ (x ◇ y) = z ◇ (x ◇ (w ◇ y))
-- Original submission SHA-256: 6794f694da56e40346c80f393b3619fc46db96046b1faa7d253785445890a380
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (((x ◇ y) ◇ y) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ (x ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc3 : forall (q0 q1 q2 q3:G), ((q2 ◇ ((q2 ◇ q2) ◇ q3)) ◇ (q0 ◇ (((q2 ◇ q0) ◇ q0) ◇ q1))) = (q0 ◇ (((q2 ◇ q0) ◇ q0) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q0 ◇ (((q2 ◇ q0) ◇ q0) ◇ q1))) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q3) (cg (fun t => t ◇ q2) ((h q2 q0 q1).symm))))).symm).trans ((h (q0 ◇ (((q2 ◇ q0) ◇ q0) ◇ q1)) q2 q3).symm)
  have apc4 : forall (q4 q5 q6:G), ((((q5 ◇ q5) ◇ (((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) ◇ q4)) ◇ (((q5 ◇ q5) ◇ (((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) ◇ q4)) ◇ q6)) ◇ q5) = q5:=by
    intro q4 q5 q6
    exact ((cg (fun t => t ◇ q5) (cg (fun t => ((q5 ◇ q5) ◇ (((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) ◇ q4)) ◇ t) (cg (fun t => t ◇ q6) (apc3 (q5 ◇ q5) q4 q5 (((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) ◇ q4))))).symm).trans ((h q5 ((q5 ◇ q5) ◇ (((q5 ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) ◇ q4)) q6).symm)
  have apc5 : forall (q7 q8:G), ((((q8 ◇ q8) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ (q8 ◇ q8)) ◇ q7)) ◇ q8) ◇ q8) = q8:=by
    intro q7 q8
    exact ((cg (fun t => t ◇ q8) (cg (fun t => ((q8 ◇ q8) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ (q8 ◇ q8)) ◇ q7)) ◇ t) ((h q8 (q8 ◇ q8) q7).symm))).symm).trans (apc4 q7 q8 q8)
  have apc6 : forall (q9:G), (q9 ◇ q9) = q9:=by
    intro q9
    exact ((cg (fun t => t ◇ q9) ((h q9 (q9 ◇ q9) q9).symm)).symm).trans (apc5 q9 q9)
  have apc7 : forall (q10 q11:G), ((q10 ◇ (q10 ◇ q11)) ◇ q10) = q10:=by
    intro q10 q11
    exact ((cg (fun t => t ◇ q10) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ q11) (apc6 q10)))).symm).trans (((cg (fun t => t ◇ q10) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ q11) (cg (fun t => t ◇ q10) (apc6 q10))))).symm).trans ((h q10 q10 q11).symm))
  have apc9 : forall (q12 q10:G), ((q10 ◇ ((q12 ◇ q10) ◇ q10)) ◇ q12) = q12:=by
    intro q12 q10
    exact ((cg (fun t => t ◇ q12) (cg (fun t => q10 ◇ t) (apc6 ((q12 ◇ q10) ◇ q10)))).symm).trans ((h q12 q10 ((q12 ◇ q10) ◇ q10)).symm)
  have apc10 : forall (q13 q14:G), (q14 ◇ (q13 ◇ ((q14 ◇ q13) ◇ q13))) = (q13 ◇ ((q14 ◇ q13) ◇ q13)):=by
    intro q13 q14
    exact ((cg (fun t => t ◇ (q13 ◇ ((q14 ◇ q13) ◇ q13))) (apc9 q14 q13)).symm).trans (((cg (fun t => t ◇ (q13 ◇ ((q14 ◇ q13) ◇ q13))) (cg (fun t => (q13 ◇ ((q14 ◇ q13) ◇ q13)) ◇ t) (apc9 q14 q13))).symm).trans (apc7 (q13 ◇ ((q14 ◇ q13) ◇ q13)) q14))
  have apc15 : forall (q15 q16 q17:G), (((q15 ◇ ((q16 ◇ q15) ◇ q15)) ◇ ((q15 ◇ ((q16 ◇ q15) ◇ q15)) ◇ q17)) ◇ q16) = q16:=by
    intro q15 q16 q17
    exact ((cg (fun t => t ◇ q16) (cg (fun t => (q15 ◇ ((q16 ◇ q15) ◇ q15)) ◇ t) (cg (fun t => t ◇ q17) (apc6 (q15 ◇ ((q16 ◇ q15) ◇ q15)))))).symm).trans (((cg (fun t => t ◇ q16) (cg (fun t => (q15 ◇ ((q16 ◇ q15) ◇ q15)) ◇ t) (cg (fun t => t ◇ q17) (cg (fun t => t ◇ (q15 ◇ ((q16 ◇ q15) ◇ q15))) (apc10 q15 q16))))).symm).trans ((h q16 (q15 ◇ ((q16 ◇ q15) ◇ q15)) q17).symm))
  have apc19 : forall (q16 q18:G), ((((q16 ◇ q18) ◇ q18) ◇ ((q18 ◇ ((q16 ◇ q18) ◇ q18)) ◇ ((q16 ◇ q18) ◇ q18))) ◇ q16) = q16:=by
    intro q16 q18
    exact ((cg (fun t => t ◇ q16) (apc10 ((q16 ◇ q18) ◇ q18) q18)).symm).trans ((h q16 q18 ((q18 ◇ ((q16 ◇ q18) ◇ q18)) ◇ ((q16 ◇ q18) ◇ q18))).symm)
  have apc20 : forall (q19 q20:G), (q20 ◇ q19) = q19:=by
    intro q19 q20
    exact ((cg (fun t => t ◇ q19) (apc19 q20 q19)).symm).trans (((cg (fun t => t ◇ q19) (cg (fun t => (((q20 ◇ q19) ◇ q19) ◇ ((q19 ◇ ((q20 ◇ q19) ◇ q19)) ◇ ((q20 ◇ q19) ◇ q19))) ◇ t) (apc19 q20 q19))).symm).trans (apc15 ((q20 ◇ q19) ◇ q19) q19 q20))
  exact (calc
    (x ◇ (x ◇ y)) = y:=(cg (fun t => x ◇ t) (apc20 y x)).trans (apc20 y x)
    _ = (z ◇ (x ◇ (w ◇ y))):=(((cg (fun t => z ◇ t) (cg (fun t => x ◇ t) (apc20 y w))).trans (cg (fun t => z ◇ t) (apc20 y x))).trans (apc20 y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_33015_to_53946 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_33015_to_53946
