-- Equation22826 → Equation35471
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ y)) ◇ ((x ◇ z) ◇ y)
-- Conclusion: x = ((x ◇ (y ◇ x)) ◇ (z ◇ z)) ◇ y
-- Original submission SHA-256: 151c036889f356c02baede7a815cac9cebde3a39c803de5501327a2e0979f859
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ ((x ◇ z) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ (y ◇ x)) ◇ (z ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (z ◇ y)) ◇ ((x ◇ z) ◇ y)) = ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ x)) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), ((q3 ◇ (((q0 ◇ q2) ◇ q1) ◇ q3)) ◇ (q0 ◇ q3)) = (q1 ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ (((q0 ◇ q2) ◇ q1) ◇ q3)) ◇ t) (cg (fun t => t ◇ q3) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (q2 ◇ q1)) q3 ((q0 ◇ q2) ◇ q1)).symm)
  have apc3 : forall (q0 q2 q4:G), ((((q0 ◇ q2) ◇ q4) ◇ ((q2 ◇ q4) ◇ ((q0 ◇ q2) ◇ q4))) ◇ q0) = q4:=by
    intro q0 q2 q4
    exact ((cg (fun t => (((q0 ◇ q2) ◇ q4) ◇ ((q2 ◇ q4) ◇ ((q0 ◇ q2) ◇ q4))) ◇ t) ((h q0 q4 q2).symm)).symm).trans ((h q4 ((q0 ◇ q2) ◇ q4) (q2 ◇ q4)).symm)
  have apc4 : forall (q5 q6 q7:G), ((q7 ◇ (((q5 ◇ q6) ◇ ((q7 ◇ q5) ◇ q6)) ◇ q7)) ◇ q6) = ((q7 ◇ q5) ◇ q6):=by
    intro q5 q6 q7
    exact ((cg (fun t => (q7 ◇ (((q5 ◇ q6) ◇ ((q7 ◇ q5) ◇ q6)) ◇ q7)) ◇ t) (apc3 q7 q5 q6)).symm).trans ((h ((q7 ◇ q5) ◇ q6) q7 ((q5 ◇ q6) ◇ ((q7 ◇ q5) ◇ q6))).symm)
  have apc5 : forall (q8:G), (q8 ◇ (((q8 ◇ q8) ◇ q8) ◇ q8)) = q8:=by
    intro q8
    exact ((apc2 (q8 ◇ q8) q8 ((q8 ◇ q8) ◇ q8) q8).symm).trans ((((cg (fun t => t ◇ ((q8 ◇ q8) ◇ q8)) (cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => ((q8 ◇ q8) ◇ ((q8 ◇ q8) ◇ q8)) ◇ t) (apc1 q8 q8 q8))))).symm).trans (apc4 (q8 ◇ q8) ((q8 ◇ q8) ◇ q8) q8)).trans (apc1 q8 ((q8 ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ q8)) ((q8 ◇ (q8 ◇ q8)) ◇ ((q8 ◇ q8) ◇ q8))))
  have apc6 : forall (q9 q10:G), (q10 ◇ ((q9 ◇ ((q10 ◇ q10) ◇ q10)) ◇ q10)) = q9:=by
    intro q9 q10
    exact ((cg (fun t => t ◇ ((q9 ◇ ((q10 ◇ q10) ◇ q10)) ◇ q10)) (apc5 q10)).symm).trans ((h q9 q10 ((q10 ◇ q10) ◇ q10)).symm)
  have apc7 : forall (q11 q12 q13:G), (q12 ◇ ((((q11 ◇ q11) ◇ q11) ◇ q11) ◇ q12)) = ((q13 ◇ ((q11 ◇ q12) ◇ q13)) ◇ (q11 ◇ q13)):=by
    intro q11 q12 q13
    exact (((cg (fun t => t ◇ (q11 ◇ q13)) (cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ q12) (apc5 q11))))).symm).trans (apc2 q11 q12 (((q11 ◇ q11) ◇ q11) ◇ q11) q13)).symm
  have apc8 : forall (q14 q15 q16:G), (((q14 ◇ (q15 ◇ q14)) ◇ (q16 ◇ q14)) ◇ q15) = q16:=by
    intro q14 q15 q16
    exact ((cg (fun t => t ◇ q15) (cg (fun t => t ◇ (q16 ◇ q14)) (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ q14) (apc6 q15 q16))))).symm).trans (((cg (fun t => t ◇ q15) (apc7 q16 ((q15 ◇ ((q16 ◇ q16) ◇ q16)) ◇ q16) q14)).symm).trans (apc3 q15 ((q16 ◇ q16) ◇ q16) q16))
  have apc9 : forall (q17 q18 q19:G), ((q19 ◇ ((q18 ◇ q17) ◇ q19)) ◇ q18) = (q17 ◇ (q19 ◇ q17)):=by
    intro q17 q18 q19
    exact ((cg (fun t => (q19 ◇ ((q18 ◇ q17) ◇ q19)) ◇ t) (apc8 q17 q19 q18)).symm).trans ((h (q17 ◇ (q19 ◇ q17)) q19 (q18 ◇ q17)).symm)
  have apc11 : forall (q20 q21:G), (q21 ◇ (((q20 ◇ q20) ◇ q21) ◇ q21)) = q21:=by
    intro q20 q21
    exact ((apc9 q21 q20 ((q20 ◇ q20) ◇ q21)).symm).trans (apc3 q20 q20 q21)
  have apc12 : forall (q22 q23:G), (q23 ◇ (q23 ◇ q23)) = (q23 ◇ (q22 ◇ q22)):=by
    intro q22 q23
    exact (((cg (fun t => t ◇ (q22 ◇ q22)) (apc11 q22 q23)).symm).trans (apc9 q23 (q22 ◇ q22) q23)).symm
  have apc13 : forall (q24 q25 q26:G), (q26 ◇ (q25 ◇ q25)) = (q26 ◇ (q24 ◇ q24)):=by
    intro q24 q25 q26
    exact (((apc12 q24 q26).symm).trans (apc12 q25 q26)).symm
  have apc201 : forall (q27 q28 q29:G), (((q28 ◇ (q29 ◇ q28)) ◇ (q27 ◇ q27)) ◇ q29) = q28:=by
    intro q27 q28 q29
    exact ((cg (fun t => t ◇ q29) (apc13 q27 q28 (q28 ◇ (q29 ◇ q28)))).symm).trans (apc8 q28 q29 q28)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (y ◇ x)) ◇ (z ◇ z)) ◇ y):=(apc201 z x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22826_to_35471 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22826_to_35471
