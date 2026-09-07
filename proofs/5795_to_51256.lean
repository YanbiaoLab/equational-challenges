-- Equation5795 → Equation51256
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((z ◇ x) ◇ x)))
-- Conclusion: x ◇ x = ((y ◇ x) ◇ (z ◇ z)) ◇ x
-- Original submission SHA-256: 9b94a747fb6e7e892ad249805fc61ba92b056f7277352f5c7b65f43d12209ad7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ ((z ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ x) ◇ (z ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (x ◇ (x ◇ ((z ◇ x) ◇ x)))) = (x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ ((q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) ◇ q0))) = (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) ◇ t) ((h q0 (q0 ◇ (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0)))) q1).symm)))).symm).trans ((h (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) q2 q0).symm)
  have apc4 : forall (q3 q4 q5 q6:G), (q6 ◇ (((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q5 ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))) ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))))) ◇ q3)) = ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q5 ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))) ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))))):=by
    intro q3 q4 q5 q6
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q5 ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))) ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))))) ◇ t) ((h q3 ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) ◇ ((q5 ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))) ◇ (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3)))))) q4).symm))).symm).trans (apc2 (q3 ◇ (q3 ◇ ((q4 ◇ q3) ◇ q3))) q5 q6)
  have apc5 : forall (q7 q8:G), (q8 ◇ (((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q7)) ◇ q7)) = ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ ((q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ q7)):=by
    intro q7 q8
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q7) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (apc1 q7 (q7 ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))) (q7 ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))))))))).symm).trans ((((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ q7) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => t ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))) (apc1 q7 q7 q7)))))).symm).trans (apc4 q7 q7 q7 q8)).trans ((cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => t ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))) (apc1 q7 (q7 ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))) (q7 ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))))))).trans (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (cg (fun t => (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7))) ◇ t) (apc1 q7 (q7 ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))) (q7 ◇ (q7 ◇ (q7 ◇ ((q7 ◇ q7) ◇ q7)))))))))
  have apc6 : forall (q9 q10:G), (q10 ◇ ((((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9) ◇ (q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))))) = (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9):=by
    intro q9 q10
    exact ((cg (fun t => q10 ◇ t) (cg (fun t => (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9) ◇ t) (apc2 q9 q9 (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9)))).symm).trans (((cg (fun t => q10 ◇ t) (cg (fun t => (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9) ◇ t) (cg (fun t => (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9) ◇ t) (apc5 q9 (q9 ◇ (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9)))))).symm).trans ((h (((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ ((q9 ◇ (q9 ◇ ((q9 ◇ q9) ◇ q9))) ◇ q9)) ◇ q9) q10 q9).symm))
  have apc7 : forall (q11 q12:G), (((q11 ◇ (q11 ◇ ((q11 ◇ q11) ◇ q11))) ◇ ((q11 ◇ (q11 ◇ ((q11 ◇ q11) ◇ q11))) ◇ q11)) ◇ q11) = (q12 ◇ q11):=by
    intro q11 q12
    exact (((cg (fun t => q12 ◇ t) ((h q11 (((q11 ◇ (q11 ◇ ((q11 ◇ q11) ◇ q11))) ◇ ((q11 ◇ (q11 ◇ ((q11 ◇ q11) ◇ q11))) ◇ q11)) ◇ q11) q11).symm)).symm).trans (apc6 q11 q12)).symm
  exact ((apc7 x x).symm).trans (apc7 x ((y ◇ x) ◇ (z ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5795_to_51256 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5795_to_51256
