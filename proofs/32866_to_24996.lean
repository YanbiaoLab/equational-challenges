-- Equation32866 → Equation24996
-- Recorded verdict: true
-- Premise: x = (x * (((y * y) * y) * z)) * z
-- Conclusion: x = (x * (y * (z * x))) * (y * x)
-- Original submission SHA-256: 68a8bb1456ea509923523d1d9e5b2cb958e58b66e92441f29abefc95fadc3a20
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (((y ◇ y) ◇ y) ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ (z ◇ x))) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc1 : forall (q0 q1 q2 q3:G), (q0 ◇ (((q1 ◇ q1) ◇ q1) ◇ (((q2 ◇ q2) ◇ q2) ◇ q3))) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ q3) ((h q0 q1 (((q2 ◇ q2) ◇ q2) ◇ q3)).symm)).symm).trans ((h (q0 ◇ (((q1 ◇ q1) ◇ q1) ◇ (((q2 ◇ q2) ◇ q2) ◇ q3))) q2 q3).symm)).symm
  have apc2 : forall (q4 q5 q6:G), ((q6 ◇ q5) ◇ (((q4 ◇ q4) ◇ q4) ◇ q5)) = q6:=by
    intro q4 q5 q6
    exact ((cg (fun t => t ◇ (((q4 ◇ q4) ◇ q4) ◇ q5)) (apc1 q6 q4 q4 q5)).symm).trans ((h q6 q4 (((q4 ◇ q4) ◇ q4) ◇ q5)).symm)
  have apc3 : forall (q7 q8 q9:G), ((q9 ◇ q8) ◇ ((q7 ◇ q7) ◇ q7)) = q9:=by
    intro q7 q8 q9
    exact ((cg (fun t => (q9 ◇ q8) ◇ t) (apc2 q7 q8 ((q7 ◇ q7) ◇ q7))).symm).trans (((cg (fun t => (q9 ◇ q8) ◇ t) ((h ((((q7 ◇ q7) ◇ q7) ◇ q8) ◇ (((q7 ◇ q7) ◇ q7) ◇ q8)) q7 q8).symm)).symm).trans (apc2 (((q7 ◇ q7) ◇ q7) ◇ q8) q8 q9))
  have apc4 : forall (q10 q11 q12:G), ((q12 ◇ q11) ◇ (q10 ◇ q11)) = q12:=by
    intro q10 q11 q12
    exact ((cg (fun t => (q12 ◇ q11) ◇ t) (cg (fun t => t ◇ q11) (apc3 q10 q10 q10))).symm).trans (((cg (fun t => (q12 ◇ q11) ◇ t) (cg (fun t => t ◇ q11) (cg (fun t => t ◇ ((q10 ◇ q10) ◇ q10)) (apc3 q10 q10 (q10 ◇ q10))))).symm).trans (apc2 ((q10 ◇ q10) ◇ q10) q11 q12))
  have apc6 : forall (q13 q14 q15:G), ((q14 ◇ (q15 ◇ q15)) ◇ (q13 ◇ q15)) = q14:=by
    intro q13 q14 q15
    exact ((cg (fun t => t ◇ (q13 ◇ q15)) (cg (fun t => q14 ◇ t) (apc4 q13 q15 (q15 ◇ q15)))).symm).trans ((h q14 q15 (q13 ◇ q15)).symm)
  have apc8 : forall (q16 q17 q18:G), ((q17 ◇ (q16 ◇ q18)) ◇ q18) = q17:=by
    intro q16 q17 q18
    exact ((cg (fun t => t ◇ q18) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q18) (apc3 q16 q16 q16)))).symm).trans (((cg (fun t => t ◇ q18) (cg (fun t => q17 ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((q16 ◇ q16) ◇ q16)) (apc3 q16 q16 (q16 ◇ q16)))))).symm).trans ((h q17 ((q16 ◇ q16) ◇ q16) q18).symm))
  have apc9 : forall (q19 q20 q21 q22:G), ((q22 ◇ q20) ◇ (q19 ◇ q21)) = q22:=by
    intro q19 q20 q21 q22
    exact ((cg (fun t => t ◇ (q19 ◇ q21)) (cg (fun t => q22 ◇ t) (apc6 q19 q20 q21))).symm).trans (apc8 (q20 ◇ (q21 ◇ q21)) q22 (q19 ◇ q21))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (y ◇ (z ◇ x))) ◇ (y ◇ x)):=(apc9 y (y ◇ (z ◇ x)) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32866_to_24996 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32866_to_24996
