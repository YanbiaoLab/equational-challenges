-- Equation46470 → Equation57386
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (w * (x * x))
-- Conclusion: x * (x * y) = ((x * y) * z) * w
-- Original submission SHA-256: 4e5a949878fb0775824a5f00ee02fd075536dfb42fd3f36dfc7831b6215adca1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ x) ◇ (w ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = ((x ◇ y) ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 (q1 ◇ q0) (q0 ◇ (q0 ◇ q0)) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), ((q4 ◇ q3) ◇ q5) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6
    exact ((((((congrArg (fun t => (q3 ◇ q3) ◇ t) (congrArg (fun t => q6 ◇ t) (apc1 q3 q4 ((q4 ◇ q3) ◇ (q4 ◇ q3))))).trans (congrArg (fun t => (q3 ◇ q3) ◇ t) (apc0 q6 (q3 ◇ q3) (q6 ◇ (q3 ◇ q3)) (q6 ◇ (q3 ◇ q3))))).trans (apc0 (q3 ◇ q3) (q6 ◇ q6) ((q3 ◇ q3) ◇ (q6 ◇ q6)) ((q3 ◇ q3) ◇ (q6 ◇ q6)))).trans (apc1 q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3)))).symm).trans (((congrArg (fun t => t ◇ (q6 ◇ ((q4 ◇ q3) ◇ (q4 ◇ q3)))) (apc1 q3 q4 q3)).symm).trans ((h (q4 ◇ q3) q5 (q4 ◇ q3) q6).symm))).symm
  exact (calc
    (x ◇ (x ◇ y)) = (x ◇ x):=(congrArg (fun t => x ◇ t) (apc0 x y (x ◇ y) (x ◇ y))).trans (apc0 x (x ◇ x) (x ◇ (x ◇ x)) (x ◇ (x ◇ x)))
    _ = (((x ◇ y) ◇ z) ◇ w):=(((congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ z) (apc0 x y (x ◇ y) (x ◇ y)))).trans (congrArg (fun t => t ◇ w) (apc2 x x z ((x ◇ x) ◇ z)))).trans (apc2 x x w ((x ◇ x) ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46470_to_57386 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46470_to_57386
