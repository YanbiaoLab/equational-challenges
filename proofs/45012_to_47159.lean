-- Equation45012 → Equation47159
-- Recorded verdict: true
-- Premise: x * y = z * ((w * (u * z)) * x)
-- Conclusion: x * y = (y * x) * ((y * y) * y)
-- Original submission SHA-256: 6e535fc4fb3f62c739732a923d13d3f048f520217ef4e62088c84391642ff67c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ ((w ◇ (u ◇ z)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ x) ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc4 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc5 : forall (x y z w u:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w u
    exact ((((congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => w ◇ t) (apc4 u z (u ◇ z) (u ◇ z) (u ◇ z))))).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (apc4 w (u ◇ u) (w ◇ (u ◇ u)) (w ◇ (u ◇ u)) (w ◇ (u ◇ u)))))).trans (apc4 z ((w ◇ w) ◇ x) (z ◇ ((w ◇ w) ◇ x)) (z ◇ ((w ◇ w) ◇ x)) (z ◇ ((w ◇ w) ◇ x)))).symm).trans ((((h x y z w u).symm).trans (h x y x x x)).trans ((congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) (apc4 x (x ◇ x) (x ◇ (x ◇ x)) (x ◇ (x ◇ x)) (x ◇ (x ◇ x))))).trans (apc4 x ((x ◇ x) ◇ x) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x)))))
  have apc6 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q0) ◇ q1) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact (((apc4 q2 (q3 ◇ q3) (q2 ◇ (q3 ◇ q3)) (q2 ◇ (q3 ◇ q3)) (q2 ◇ (q3 ◇ q3))).symm).trans ((((congrArg (fun t => q2 ◇ t) (apc5 q3 q3 (q0 ◇ (q4 ◇ q2)) q3 q3)).symm).trans ((h (q0 ◇ (q4 ◇ q2)) q1 q2 q0 q4).symm)).trans ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q0 ◇ t) (apc4 q4 q2 (q4 ◇ q2) (q4 ◇ q2) (q4 ◇ q2)))).trans (congrArg (fun t => t ◇ q1) (apc4 q0 (q4 ◇ q4) (q0 ◇ (q4 ◇ q4)) (q0 ◇ (q4 ◇ q4)) (q0 ◇ (q4 ◇ q4))))))).symm
  have apc7 : forall (q5 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q6 ◇ q6):=by
    intro q5 q6
    exact (((apc6 q5 q5 q6 q5 q5).symm).trans (apc4 (q5 ◇ q5) q5 q5 q5 q5)).symm
  have apc13 : forall (q7 q8 q9 q10:G), (((q7 ◇ q7) ◇ q8) ◇ (q9 ◇ q9)) = (q10 ◇ q10):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ (q9 ◇ q9)) ((apc6 q7 q8 q9 q7 q7).symm)).symm).trans (apc7 q9 q10)
  have apc14 : forall (q11 q12 q13 q14 q15:G), (((q13 ◇ q13) ◇ q14) ◇ ((q11 ◇ q11) ◇ q12)) = (q15 ◇ q15):=by
    intro q11 q12 q13 q14 q15
    exact ((congrArg (fun t => ((q13 ◇ q13) ◇ q14) ◇ t) ((apc6 q11 q12 q11 q11 q11).symm)).symm).trans (apc13 q13 q14 q11 q15)
  have apc15 : forall (q16 q17 q18:G), (q18 ◇ q18) = (q17 ◇ q16):=by
    intro q16 q17 q18
    exact ((h q17 q16 ((q16 ◇ q16) ◇ q16) (q16 ◇ ((q16 ◇ q16) ◇ q16)) q16).trans (apc14 (q16 ◇ ((q16 ◇ q16) ◇ q16)) q17 q16 q16 q18)).symm
  exact ((apc15 y x (x ◇ y)).symm).trans (apc15 ((y ◇ y) ◇ y) (y ◇ x) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45012_to_47159 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45012_to_47159
