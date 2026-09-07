-- Equation15317 → Equation14497
-- Recorded verdict: true
-- Premise: x = x * (((y * (y * x)) * z) * w)
-- Conclusion: x = x * (((y * z) * (y * w)) * x)
-- Original submission SHA-256: 6876fe43d9f5d72291e1e9141866b329e06070c3623f084456e8d710cd71e89e
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ (y ◇ x)) ◇ z) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ z) ◇ (y ◇ w)) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ (q1 ◇ q0)) ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) ((h ((q1 ◇ (q1 ◇ q0)) ◇ q2) q0 q0 q0).symm)).symm).trans ((h q0 q1 q2 (((q0 ◇ (q0 ◇ ((q1 ◇ (q1 ◇ q0)) ◇ q2))) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ (q4 ◇ (q4 ◇ q3))) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (apc0 (q4 ◇ (q4 ◇ q3)) q3 q3)).symm).trans (apc0 q3 q4 ((q3 ◇ (q3 ◇ (q4 ◇ (q4 ◇ q3)))) ◇ q3))
  have apc2 : forall (q5:G), ((q5 ◇ q5) ◇ q5) = (q5 ◇ q5):=by
    intro q5
    exact ((congrArg (fun t => (q5 ◇ q5) ◇ t) (apc1 q5 q5)).symm).trans (apc1 (q5 ◇ q5) q5)
  have apc4 : forall (q6:G), (q6 ◇ ((q6 ◇ q6) ◇ (q6 ◇ q6))) = q6:=by
    intro q6
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => (q6 ◇ q6) ◇ t) (apc2 q6))).symm).trans (apc1 q6 (q6 ◇ q6))
  have apc8 : forall (q7 q8:G), ((q7 ◇ q7) ◇ (q7 ◇ q8)) = (q7 ◇ q7):=by
    intro q7 q8
    exact ((congrArg (fun t => (q7 ◇ q7) ◇ t) (congrArg (fun t => t ◇ q8) (apc1 q7 q7))).symm).trans (apc0 (q7 ◇ q7) q7 q8)
  have apc10 : forall (q7 q8 q6:G), (q6 ◇ (q6 ◇ q6)) = q6:=by
    intro q7 q8 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc8 q6 q6)).symm).trans (apc4 q6)
  have apc13 : forall (q9 q10:G), (q9 ◇ (q9 ◇ q10)) = q9:=by
    intro q9 q10
    exact ((congrArg (fun t => q9 ◇ t) (congrArg (fun t => t ◇ q10) (apc10 q9 q9 q9))).symm).trans (apc0 q9 q9 q10)
  have apc15 : forall (q0 q1 q2 q9 q10:G), (q0 ◇ (q1 ◇ q2)) = q0:=by
    intro q0 q1 q2 q9 q10
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => t ◇ q2) (apc13 q1 q0))).symm).trans (apc0 q0 q1 q2)
  exact (apc15 x ((y ◇ z) ◇ (y ◇ w)) x x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15317_to_14497 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15317_to_14497
