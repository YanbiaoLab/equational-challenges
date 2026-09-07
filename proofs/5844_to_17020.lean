-- Equation5844 → Equation17020
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (y ◇ ((z ◇ w) ◇ x)))
-- Conclusion: x = (x ◇ x) ◇ (y ◇ (z ◇ (w ◇ x)))
-- Original submission SHA-256: 9c8fa748a2a8560e46da93519bd7330c4fada6129c4425e0913cacce43208367
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ (y ◇ ((z ◇ w) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ x) ◇ (y ◇ (z ◇ (w ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ q2) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) ((h q2 ((q1 ◇ q0) ◇ q2) q1 q0).symm)).symm).trans ((h ((q1 ◇ q0) ◇ q2) q2 (q1 ◇ q0) q2).symm)).symm
  have apc1 : forall (q3 q4:G), (q4 ◇ q4) = (q3 ◇ q4):=by
    intro q3 q4
    exact (((cg (fun t => t ◇ q4) ((h q3 q3 q3 q3).symm)).symm).trans (apc0 (q3 ◇ (q3 ◇ ((q3 ◇ q3) ◇ q3))) q3 q4)).symm
  have apc2 : forall (q5 q6 q7:G), (q6 ◇ q7) = (q5 ◇ q7):=by
    intro q5 q6 q7
    exact (((apc1 q5 q7).symm).trans (apc1 q6 q7)).symm
  have apc3 : forall (q8 q9 q10:G), (q10 ◇ (q9 ◇ (q10 ◇ (q8 ◇ q9)))) = q9:=by
    intro q8 q9 q10
    exact ((cg (fun t => q10 ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ q9) ((h q8 q8 q8 q8).symm))))).symm).trans ((h q9 q10 q8 (q8 ◇ (q8 ◇ ((q8 ◇ q8) ◇ q8)))).symm)
  have apc4 : forall (q11 q12 q13:G), (q13 ◇ (q12 ◇ q12)) = (q13 ◇ (q11 ◇ q12)):=by
    intro q11 q12 q13
    exact ((cg (fun t => q13 ◇ t) (apc0 (q11 ◇ q12) q13 q12)).symm).trans (((cg (fun t => q13 ◇ t) (cg (fun t => (q13 ◇ (q11 ◇ q12)) ◇ t) (apc3 q11 q12 q13))).symm).trans (apc3 q12 (q13 ◇ (q11 ◇ q12)) q13))
  have apc6 : forall (q14 q15 q16 q17:G), (q17 ◇ (q14 ◇ q15)) = (q16 ◇ (q15 ◇ q15)):=by
    intro q14 q15 q16 q17
    exact ((apc4 q14 q15 q17).symm).trans (apc2 q16 q17 (q15 ◇ q15))
  have apc9 : forall (q14 q15 q16 q17:G), (q17 ◇ (q14 ◇ q15)) = (q15 ◇ (q15 ◇ q15)):=by
    intro q14 q15 q16 q17
    exact (apc6 q14 q15 q14 q17).trans ((apc6 q15 q15 q14 q15).symm)
  have apc16 : forall (x y z w q0 q1 q2:G), (y ◇ (x ◇ (x ◇ (x ◇ x)))) = x:=by
    intro x y z w q0 q1 q2
    exact (((h x y x x).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => y ◇ t) (apc0 x x x))))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (apc9 x x (y ◇ (x ◇ x)) y)))).symm
  have apc21 : forall (q18 q19 q20:G), (q20 ◇ (q19 ◇ (q19 ◇ (q18 ◇ q19)))) = q19:=by
    intro q18 q19 q20
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (apc1 q18 q19)))).symm).trans (apc16 q19 q20 q18 q18 q18 q18 q18)
  have apc23 : forall (q21 q22 q23 q24:G), (q24 ◇ (q21 ◇ (q23 ◇ (q22 ◇ q23)))) = q23:=by
    intro q21 q22 q23 q24
    exact ((cg (fun t => q24 ◇ t) (apc2 q21 q23 (q23 ◇ (q22 ◇ q23)))).symm).trans (apc21 q22 q23 q24)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ x) ◇ (y ◇ (z ◇ (w ◇ x)))):=((cg (fun t => (x ◇ x) ◇ t) (cg (fun t => y ◇ t) (apc9 w x (z ◇ (w ◇ x)) z))).trans (apc23 y x x (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5844_to_17020 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5844_to_17020
