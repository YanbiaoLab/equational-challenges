-- Equation39125 → Equation41853
-- Recorded verdict: true
-- Premise: x = (((y * x) * (x * z)) * y) * x
-- Conclusion: x * y = x * (z * (z * (w * y)))
-- Original submission SHA-256: c46e233eb4e2800c62733c233fd4a6166fce54f7a816817660883c7b5935e76c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ (x ◇ z)) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (z ◇ (z ◇ (w ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q2) ◇ ((q1 ◇ (q1 ◇ q2)) ◇ ((q1 ◇ q2) ◇ q0))) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q1 ◇ (q1 ◇ q2)) ◇ ((q1 ◇ q2) ◇ q0))) ((h (q1 ◇ q2) q1 q0).symm))).symm).trans ((h q1 ((q1 ◇ (q1 ◇ q2)) ◇ ((q1 ◇ q2) ◇ q0)) q2).symm)
  have apc4 : forall (q3 q4 q5 q6:G), (((q5 ◇ (q5 ◇ q6)) ◇ ((q5 ◇ q4) ◇ ((q5 ◇ (q5 ◇ q4)) ◇ ((q5 ◇ q4) ◇ q3)))) ◇ q5) = q5:=by
    intro q3 q4 q5 q6
    exact ((cg (fun t => t ◇ q5) (cg (fun t => t ◇ ((q5 ◇ q4) ◇ ((q5 ◇ (q5 ◇ q4)) ◇ ((q5 ◇ q4) ◇ q3)))) (cg (fun t => t ◇ (q5 ◇ q6)) (apc0 q3 q5 q4)))).symm).trans ((h q5 ((q5 ◇ q4) ◇ ((q5 ◇ (q5 ◇ q4)) ◇ ((q5 ◇ q4) ◇ q3))) q6).symm)
  have apc5 : forall (q7 q0 q8 q2:G), ((((q8 ◇ (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)) ◇ q2) ◇ q8) ◇ (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)) = (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7):=by
    intro q7 q0 q8 q2
    exact ((cg (fun t => t ◇ (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)) (cg (fun t => t ◇ q8) (cg (fun t => (q8 ◇ (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)) ◇ t) ((h q2 q7 q0).symm)))).symm).trans ((h (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7) q8 q2).symm)
  have apc6 : forall (q9 q10:G), (q10 ◇ (q10 ◇ q9)) = (q10 ◇ q9):=by
    intro q9 q10
    exact ((cg (fun t => t ◇ (q10 ◇ q9)) (apc4 q9 q9 q10 q9)).symm).trans ((h (q10 ◇ q9) q10 ((q10 ◇ (q10 ◇ q9)) ◇ ((q10 ◇ q9) ◇ q9))).symm)
  have apc8 : forall (q0 q1 q2 q9 q10:G), (((q1 ◇ q2) ◇ q0) ◇ q1) = q1:=by
    intro q0 q1 q2 q9 q10
    exact ((((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ q2) ◇ t) (cg (fun t => t ◇ ((q1 ◇ q2) ◇ q0)) (apc6 q2 q1)))).trans (cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ q2) ◇ t) (apc6 q0 (q1 ◇ q2))))).trans (cg (fun t => t ◇ q1) (apc6 q0 (q1 ◇ q2)))).symm).trans (apc0 q0 q1 q2)
  have apc9 : forall (q7 q0 q1 q8 q2 q9 q10:G), (q8 ◇ q7) = q7:=by
    intro q7 q0 q1 q8 q2 q9 q10
    exact ((((cg (fun t => t ◇ (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)) (cg (fun t => t ◇ q8) (cg (fun t => t ◇ q2) (cg (fun t => q8 ◇ t) (apc8 (q2 ◇ q0) q7 q2 (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7) (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)))))).trans (cg (fun t => t ◇ (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)) (apc8 q2 q8 q7 (((q8 ◇ q7) ◇ q2) ◇ q8) (((q8 ◇ q7) ◇ q2) ◇ q8)))).trans (cg (fun t => q8 ◇ t) (apc8 (q2 ◇ q0) q7 q2 (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7) (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)))).symm).trans ((apc5 q7 q0 q8 q2).trans (apc8 (q2 ◇ q0) q7 q2 (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7) (((q7 ◇ q2) ◇ (q2 ◇ q0)) ◇ q7)))
  exact (calc
    (x ◇ y) = y:=apc9 y (x ◇ y) (x ◇ y) x (x ◇ y) (x ◇ y) (x ◇ y)
    _ = (x ◇ (z ◇ (z ◇ (w ◇ y)))):=((((cg (fun t => x ◇ t) (cg (fun t => z ◇ t) (cg (fun t => z ◇ t) (apc9 y (w ◇ y) (w ◇ y) w (w ◇ y) (w ◇ y) (w ◇ y))))).trans (cg (fun t => x ◇ t) (cg (fun t => z ◇ t) (apc9 y (z ◇ y) (z ◇ y) z (z ◇ y) (z ◇ y) (z ◇ y))))).trans (cg (fun t => x ◇ t) (apc9 y (z ◇ y) (z ◇ y) z (z ◇ y) (z ◇ y) (z ◇ y)))).trans (apc9 y (x ◇ y) (x ◇ y) x (x ◇ y) (x ◇ y) (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_39125_to_41853 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_39125_to_41853
