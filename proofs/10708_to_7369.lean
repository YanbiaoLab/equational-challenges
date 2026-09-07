-- Equation10708 → Equation7369
-- Recorded verdict: true
-- Premise: x = y * ((z * w) * ((x * w) * x))
-- Conclusion: x = x * (x * ((y * (z * z)) * x))
-- Original submission SHA-256: 9066df5573280adc01bc93873c16e19afbe854aec7318d8dfb9140e58c0737cd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ w) ◇ ((x ◇ w) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (x ◇ ((y ◇ (z ◇ z)) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ (q1 ◇ ((q3 ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q0) ◇ q1))) ◇ q3))) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => t ◇ ((q3 ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q0) ◇ q1))) ◇ q3)) ((h q1 q0 q2 q0).symm))).symm).trans ((h q3 q4 q0 ((q2 ◇ q0) ◇ ((q1 ◇ q0) ◇ q1))).symm)
  have apc1 : forall (q5 q6 q7 q8 q9 q10:G), (q7 ◇ (q5 ◇ (q5 ◇ q6))) = q6:=by
    intro q5 q6 q7 q8 q9 q10
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => t ◇ q6) (apc0 q8 q9 q10 q5 q6)))).symm).trans (((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ ((q6 ◇ (q9 ◇ ((q5 ◇ ((q10 ◇ q8) ◇ ((q9 ◇ q8) ◇ q9))) ◇ q5))) ◇ q6)) (apc0 q8 q9 q10 q5 q8))).symm).trans ((h q6 q7 q8 (q9 ◇ ((q5 ◇ ((q10 ◇ q8) ◇ ((q9 ◇ q8) ◇ q9))) ◇ q5))).symm))
  have apc3 : forall (q11 q12 q13 q14 q15 q16:G), (q16 ◇ ((q11 ◇ (q11 ◇ q12)) ◇ ((q15 ◇ ((q14 ◇ q13) ◇ q12)) ◇ q15))) = q15:=by
    intro q11 q12 q13 q14 q15 q16
    exact ((cg (fun t => q16 ◇ t) (cg (fun t => (q11 ◇ (q11 ◇ q12)) ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => q15 ◇ t) (cg (fun t => (q14 ◇ q13) ◇ t) (apc1 q11 q12 ((q11 ◇ (q11 ◇ q12)) ◇ q13) q11 q11 q11)))))).symm).trans (apc0 q13 (q11 ◇ (q11 ◇ q12)) q14 q15 q16)
  have apc4 : forall (q17 q18 q19 q20 q21:G), (q21 ◇ ((q18 ◇ (q18 ◇ q19)) ◇ ((q20 ◇ (q17 ◇ q19)) ◇ q20))) = q20:=by
    intro q17 q18 q19 q20 q21
    exact ((cg (fun t => q21 ◇ t) (cg (fun t => (q18 ◇ (q18 ◇ q19)) ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q19) (apc1 q17 q17 q17 q17 q17 q17)))))).symm).trans (apc3 q18 q19 (q17 ◇ (q17 ◇ q17)) q17 q20 q21)
  have apc5 : forall (q22 q23 q24 q25 q26:G), (q26 ◇ (q22 ◇ ((q25 ◇ (q23 ◇ (q24 ◇ q22))) ◇ q25))) = q25:=by
    intro q22 q23 q24 q25 q26
    exact ((cg (fun t => q26 ◇ t) (cg (fun t => t ◇ ((q25 ◇ (q23 ◇ (q24 ◇ q22))) ◇ q25)) (apc1 q24 q22 q24 q22 q22 q22))).symm).trans (apc4 q23 q24 (q24 ◇ q22) q25 q26)
  have apc6 : forall (q1 q27 q4:G), ((q1 ◇ q27) ◇ q1) = (q4 ◇ q1):=by
    intro q1 q27 q4
    exact (((cg (fun t => q4 ◇ t) ((h q1 (q1 ◇ q27) ((q1 ◇ q27) ◇ q1) q27).symm)).symm).trans ((h ((q1 ◇ q27) ◇ q1) q4 q1 q27).symm)).symm
  have apc9 : forall (q28 q29 q30 q31:G), (q31 ◇ (q29 ◇ (q28 ◇ q30))) = q30:=by
    intro q28 q29 q30 q31
    exact ((cg (fun t => q31 ◇ t) (cg (fun t => q29 ◇ t) (apc6 q30 (q28 ◇ (q28 ◇ q29)) q28))).symm).trans (apc5 q29 q28 q28 q30 q31)
  exact (apc9 (y ◇ (z ◇ z)) x x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10708_to_7369 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10708_to_7369
