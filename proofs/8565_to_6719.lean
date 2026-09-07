-- Equation8565 → Equation6719
-- Recorded verdict: true
-- Premise: x = y ◇ (y ◇ (((x ◇ x) ◇ z) ◇ z))
-- Conclusion: x = y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ z)))
-- Original submission SHA-256: 0c2f533917ca7a23bdf0914b523d76eaf1c79bc3ec59d66412cb5cf36c8dd3e3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (((x ◇ x) ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ (q3 ◇ (q0 ◇ ((q2 ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ ((q2 ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) ((h q0 (q2 ◇ q2) q1).symm)))).symm).trans ((h q2 q3 ((q2 ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))).symm)
  have apc1 : forall (q4 q5:G), (q5 ◇ (q5 ◇ (q4 ◇ q4))) = q4:=by
    intro q4 q5
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => q5 ◇ t) ((h (q4 ◇ q4) (q4 ◇ q4) q4).symm))).symm).trans (apc0 (q4 ◇ q4) q4 q4 q5)
  have apc2 : forall (q6 q7:G), (q6 ◇ q6) = q6:=by
    intro q6 q7
    exact (((apc1 q6 q7).symm).trans (((cg (fun t => q7 ◇ t) (cg (fun t => q7 ◇ t) (cg (fun t => q6 ◇ t) (apc1 q6 ((q6 ◇ q6) ◇ (q6 ◇ q6)))))).symm).trans (apc0 q6 (q6 ◇ q6) (q6 ◇ q6) q7))).symm
  have apc4 : forall (q4 q5 q6 q7:G), (q5 ◇ (q5 ◇ q4)) = q4:=by
    intro q4 q5 q6 q7
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => q5 ◇ t) (apc2 q4 (q4 ◇ q4)))).symm).trans (apc1 q4 q5)
  have apc5 : forall (x y z:G), ((x ◇ z) ◇ z) = x:=by
    intro x y z
    exact (((cg (fun t => y ◇ t) (cg (fun t => y ◇ t) (cg (fun t => t ◇ z) (cg (fun t => t ◇ z) (apc2 x (x ◇ x)))))).trans (apc4 ((x ◇ z) ◇ z) y (y ◇ (y ◇ ((x ◇ z) ◇ z))) (y ◇ (y ◇ ((x ◇ z) ◇ z))))).symm).trans ((((h x y z).symm).trans (h x x x)).trans (((((cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc2 x (x ◇ x)))))).trans (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => t ◇ x) (apc2 x (x ◇ x)))))).trans (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (apc2 x (x ◇ x))))).trans (cg (fun t => x ◇ t) (apc2 x (x ◇ x)))).trans (apc2 x (x ◇ x))))
  have apc6 : forall (q8 q9 q10:G), (q8 ◇ (q9 ◇ q8)) = q9:=by
    intro q8 q9 q10
    exact (((cg (fun t => q10 ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q8) (apc2 q9 (q9 ◇ q9)))))).trans (apc4 (q8 ◇ (q9 ◇ q8)) q10 (q10 ◇ (q10 ◇ (q8 ◇ (q9 ◇ q8)))) (q10 ◇ (q10 ◇ (q8 ◇ (q9 ◇ q8)))))).symm).trans (((cg (fun t => q10 ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ ((q9 ◇ q9) ◇ q8)) (apc4 q8 (q9 ◇ q9) q8 q8)))).symm).trans ((h q9 q10 ((q9 ◇ q9) ◇ q8)).symm))
  exact (calc
    x = x:=rfl
    _ = (y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ z)))):=(((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => (y ◇ z) ◇ t) (apc2 z (z ◇ z))))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (apc5 y ((y ◇ z) ◇ z) z)))).trans (apc6 y x (y ◇ (x ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8565_to_6719 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8565_to_6719
