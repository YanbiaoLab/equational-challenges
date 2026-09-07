-- Equation40215 → Equation9574
-- Recorded verdict: true
-- Premise: x = (((y * (y * z)) * x) * w) * x
-- Conclusion: x = y * ((y * z) * (w * (w * x)))
-- Original submission SHA-256: 7d662ef6ee295852da58c662fcb4f0f00b820237826c63758c9f03cbfc63d34f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ (y ◇ z)) ◇ x) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((y ◇ z) ◇ (w ◇ (w ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q0) ((h q1 q0 q0 (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q0)).symm))).symm).trans ((h q1 ((q0 ◇ (q0 ◇ q0)) ◇ q1) q0 q0).symm)
  have apc1 : forall (q2 q3:G), (q3 ◇ (q3 ◇ q2)) = (q3 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) (apc0 q2 q3)).symm).trans (apc0 q3 (q3 ◇ q2))
  have apc2 : forall (q4 q5 q6:G), ((q5 ◇ q6) ◇ q4) = q4:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q4) (apc1 q6 q5)).symm).trans (((congrArg (fun t => t ◇ q4) (apc0 q4 (q5 ◇ (q5 ◇ q6)))).symm).trans ((h q4 q5 q6 (q5 ◇ (q5 ◇ q6))).symm))
  have apc3 : forall (q7 q8:G), (q8 ◇ q7) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ q7) (apc2 q8 q7 q7)).symm).trans (apc2 q7 (q7 ◇ q7) q8)
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((y ◇ z) ◇ (w ◇ (w ◇ x)))):=(((((congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) (congrArg (fun t => w ◇ t) (apc3 x w)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (y ◇ z) ◇ t) (apc3 x w)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (apc3 z y)))).trans (congrArg (fun t => y ◇ t) (apc3 x z))).trans (apc3 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40215_to_9574 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40215_to_9574
