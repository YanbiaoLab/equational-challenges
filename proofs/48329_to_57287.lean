-- Equation48329 → Equation57287
-- Recorded verdict: true
-- Premise: x * y = (z * (z * x)) * (x * z)
-- Conclusion: x * (y * z) = (w * (u * y)) * w
-- Original submission SHA-256: c72ba5b1a0ae86f7c84c0b2bd71d836374cdb9b0717e7d5797bb721254045ac2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (z ◇ x)) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (w ◇ (u ◇ y)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ q1) ◇ t) (apc0 q0 q1 (q0 ◇ q1))).symm).trans ((((congrArg (fun t => t ◇ (q0 ◇ q1)) (apc0 q1 (q1 ◇ q0) q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2)))
  have apc2 : forall (q3 q4:G), ((q3 ◇ q3) ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4
    exact (((((congrArg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).trans (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3))))).trans (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (apc1 (q3 ◇ q3) q3 q3)).symm).trans ((h (q3 ◇ q3) q4 (q3 ◇ q3)).symm))).symm
  have apc3 : forall (q5 q3 q4:G), (q3 ◇ q3) = (q5 ◇ q5):=by
    intro q5 q3 q4
    exact ((((((congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => (q5 ◇ q5) ◇ t) (apc0 (q5 ◇ q5) (q3 ◇ q3) ((q5 ◇ q5) ◇ (q3 ◇ q3))))).trans (congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => (q5 ◇ q5) ◇ t) (apc2 q5 (q5 ◇ q5))))).trans (congrArg (fun t => t ◇ (q5 ◇ q5)) (apc2 q5 (q5 ◇ q5)))).trans (apc2 q5 (q5 ◇ q5))).symm).trans ((((congrArg (fun t => ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ (q3 ◇ q3))) ◇ t) (apc1 q5 q3 q5)).symm).trans ((h (q3 ◇ q3) q4 (q5 ◇ q5)).symm)).trans (apc2 q3 q4))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc0 x (y ◇ z) u
    _ = ((w ◇ (u ◇ y)) ◇ (w ◇ (u ◇ y))):=(apc3 x (w ◇ (u ◇ y)) u).symm
    _ = ((w ◇ (u ◇ y)) ◇ w):=(apc0 (w ◇ (u ◇ y)) w u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48329_to_57287 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48329_to_57287
