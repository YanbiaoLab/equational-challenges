-- Equation30488 → Equation18059
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ ((x ◇ x) ◇ z))) ◇ x
-- Conclusion: x = (y ◇ x) ◇ (x ◇ ((x ◇ z) ◇ x))
-- Original submission SHA-256: 11864584937d1804faa2b94b6b91440b59886b5ca17633f45d31634de0009cc1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ ((x ◇ x) ◇ z))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (x ◇ ((x ◇ z) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3:G), (((q0 ◇ (q0 ◇ ((((q2 ◇ q2) ◇ q3) ◇ ((q2 ◇ q2) ◇ q3)) ◇ q1))) ◇ ((q2 ◇ q2) ◇ q3)) ◇ q2) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q2) (cg (fun t => (q0 ◇ (q0 ◇ ((((q2 ◇ q2) ◇ q3) ◇ ((q2 ◇ q2) ◇ q3)) ◇ q1))) ◇ t) ((h ((q2 ◇ q2) ◇ q3) q0 q1).symm))).symm).trans ((h q2 (q0 ◇ (q0 ◇ ((((q2 ◇ q2) ◇ q3) ◇ ((q2 ◇ q2) ◇ q3)) ◇ q1))) q3).symm)
  have apc3 : forall (q4 q5:G), (((q4 ◇ q4) ◇ q5) ◇ q4) = q4:=by
    intro q4 q5
    exact ((cg (fun t => t ◇ q4) ((h ((q4 ◇ q4) ◇ q5) q4 q4).symm)).symm).trans (apc2 q4 q4 q4 q5)
  have apc4 : forall (q6:G), (q6 ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q6
    exact ((cg (fun t => t ◇ (q6 ◇ q6)) (apc3 q6 (q6 ◇ q6))).symm).trans (apc3 (q6 ◇ q6) q6)
  have apc5 : forall (q7 q8:G), ((q7 ◇ (q7 ◇ q8)) ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q7 q8
    exact ((cg (fun t => t ◇ (q8 ◇ q8)) (cg (fun t => q7 ◇ t) (cg (fun t => q7 ◇ t) (apc3 q8 (q8 ◇ q8))))).symm).trans ((h (q8 ◇ q8) q7 q8).symm)
  have apc6 : forall (q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = (q9 ◇ q9):=by
    intro q9
    exact ((cg (fun t => t ◇ (q9 ◇ q9)) (apc4 q9)).symm).trans (apc5 q9 q9)
  have apc7 : forall (q10:G), ((q10 ◇ q10) ◇ q10) = q10:=by
    intro q10
    exact ((cg (fun t => t ◇ q10) (apc6 q10)).symm).trans (apc3 q10 (q10 ◇ q10))
  have apc8 : forall (q11:G), (q11 ◇ q11) = q11:=by
    intro q11
    exact ((cg (fun t => t ◇ q11) (apc7 q11)).symm).trans (apc3 q11 q11)
  have apc9 : forall (q4 q5 q11:G), ((q4 ◇ q5) ◇ q4) = q4:=by
    intro q4 q5 q11
    exact ((cg (fun t => t ◇ q4) (cg (fun t => t ◇ q5) (apc8 q4))).symm).trans (apc3 q4 q5)
  have apc11 : forall (q12 q13:G), ((q12 ◇ (q12 ◇ q13)) ◇ q13) = q13:=by
    intro q12 q13
    exact ((cg (fun t => t ◇ q13) (cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (apc7 q13)))).symm).trans ((h q13 q12 q13).symm)
  have apc12 : forall (q14 q15:G), (q15 ◇ (q15 ◇ q14)) = (q15 ◇ q14):=by
    intro q14 q15
    exact ((cg (fun t => t ◇ (q15 ◇ q14)) (apc9 q15 q14 q14)).symm).trans (apc9 (q15 ◇ q14) q15 q14)
  have apc13 : forall (q14 q15 q12 q13:G), ((q12 ◇ q13) ◇ q13) = q13:=by
    intro q14 q15 q12 q13
    exact ((cg (fun t => t ◇ q13) (apc12 q13 q12)).symm).trans (apc11 q12 q13)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ x) ◇ (x ◇ ((x ◇ z) ◇ x))):=(((cg (fun t => (y ◇ x) ◇ t) (cg (fun t => x ◇ t) (apc9 x z ((x ◇ z) ◇ x)))).trans (cg (fun t => (y ◇ x) ◇ t) (apc8 x))).trans (apc13 ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30488_to_18059 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30488_to_18059
