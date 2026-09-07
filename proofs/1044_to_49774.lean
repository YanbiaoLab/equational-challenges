-- Equation1044 → Equation49774
-- Recorded verdict: true
-- Premise: x = x * ((y * (x * z)) * w)
-- Conclusion: x * y = (x * (z * (w * u))) * u
-- Original submission SHA-256: 9f50343b9bb529b6589cf52c3831d181333b58362e85e677928aa520c1efcbe2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ (x ◇ z)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (x ◇ (z ◇ (w ◇ u))) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ (q3 ◇ q1)) ◇ (q3 ◇ q2)) = (q0 ◇ (q3 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q0 ◇ (q3 ◇ q1)) ◇ t) (congrArg (fun t => t ◇ q2) ((h q3 q0 q1 q0).symm))).symm).trans ((h (q0 ◇ (q3 ◇ q1)) q3 q0 q2).symm)
  have apc1 : forall (q4 q5 q6:G), ((q4 ◇ (q6 ◇ q5)) ◇ q6) = (q4 ◇ (q6 ◇ q5)):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => (q4 ◇ (q6 ◇ q5)) ◇ t) ((h q6 q4 q4 q4).symm)).symm).trans (apc0 q4 q5 ((q4 ◇ (q6 ◇ q4)) ◇ q4) q6)
  have apc2 : forall (q7 q3 q8:G), (q7 ◇ (q3 ◇ (q7 ◇ q8))) = q7:=by
    intro q7 q3 q8
    exact ((congrArg (fun t => q7 ◇ t) ((h (q3 ◇ (q7 ◇ q8)) q7 q7 q7).symm)).symm).trans ((h q7 q3 q8 ((q7 ◇ ((q3 ◇ (q7 ◇ q8)) ◇ q7)) ◇ q7)).symm)
  have apc4 : forall (q9 q10 q11:G), (q9 ◇ q10) = q9:=by
    intro q9 q10 q11
    exact (((congrArg (fun t => t ◇ q10) (apc2 q9 q10 q11)).symm).trans (apc1 q9 (q9 ◇ q11) q10)).trans (apc2 q9 q10 q11)
  exact (calc
    (x ◇ y) = x:=apc4 x y (x ◇ y)
    _ = ((x ◇ (z ◇ (w ◇ u))) ◇ u):=((((congrArg (fun t => t ◇ u) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (apc4 w u (w ◇ u))))).trans (congrArg (fun t => t ◇ u) (congrArg (fun t => x ◇ t) (apc4 z w (z ◇ w))))).trans (congrArg (fun t => t ◇ u) (apc4 x z (x ◇ z)))).trans (apc4 x u (x ◇ u))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1044_to_49774 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1044_to_49774
