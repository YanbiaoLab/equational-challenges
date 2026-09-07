-- Equation59913 → Equation59688
-- Recorded verdict: true
-- Premise: (x * y) * z = w * ((u * x) * u)
-- Conclusion: (x * y) * z = y * ((z * x) * w)
-- Original submission SHA-256: 7ad9df899f75ce5ccdc3623dbb7db273bdcc99a5dc731c586dd0a94f85f408c3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = w ◇ ((u ◇ x) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = y ◇ ((z ◇ x) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc5 : forall (x y z w u : G), (x ◇ ((x ◇ x) ◇ x)) = (w ◇ ((u ◇ x) ◇ u)) := by
    intro x y z w u
    exact (((rfl).symm).trans (((h x y z w u).symm.trans (h x y z x x)).trans (rfl))).symm
  have apc6 : forall (q0 q1 q2 : G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q1) ◇ q2) := by
    intro q0 q1 q2
    exact ((rfl).symm).trans (((((apc5 q0 q0 q0 q0 q0).symm).symm).trans ((h q0 q1 q2 q0 q0).symm)).trans (rfl))
  have apc11 : forall (x y z w u : G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ x) := by
    intro x y z w u
    exact ((rfl).symm).trans (((h x y z w u).trans ((h x x x w u).symm)).trans (rfl))
  have apc13 : forall (x y z w u q0 q1 q2 : G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ q0) := by
    intro x y z w u q0 q1 q2
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc6 q0 q1 q2).trans (apc11 q0 q1 q2 ((q0 ◇ q1) ◇ q2) ((q0 ◇ q1) ◇ q2)))).trans (rfl))
  have apc17 : forall (q3 q4 q5 q6 q7 q8 q9 : G), (q6 ◇ (q4 ◇ ((q3 ◇ q3) ◇ q3))) = ((q7 ◇ q7) ◇ q7) := by
    intro q3 q4 q5 q6 q7 q8 q9
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q4 ◇ t) (apc11 q3 q5 q3 ((q3 ◇ q5) ◇ q3) ((q3 ◇ q5) ◇ q3)))).symm).trans ((((congrArg (fun t => q6 ◇ t) (h q5 q7 q5 q4 q3)).symm).trans ((h q7 q8 q9 q6 q5).symm)).trans (apc11 q7 q8 q9 ((q7 ◇ q8) ◇ q9) ((q7 ◇ q8) ◇ q9)))
  have apc18 : forall (q10 q11 q12 q13 q14 : G), (q13 ◇ ((q12 ◇ q10) ◇ q11)) = ((q14 ◇ q14) ◇ q14) := by
    intro q10 q11 q12 q13 q14
    exact ((rfl).symm).trans ((((congrArg (fun t => q13 ◇ t) ((h q12 q10 q11 q10 q12).symm)).symm).trans (apc17 q12 q10 q10 q13 q14 q10 q10)).trans (rfl))
  have apc47 : forall (q15 q16 q17 q18 q19 : G), (q19 ◇ (q18 ◇ ((q17 ◇ q15) ◇ q16))) = ((q19 ◇ q19) ◇ q19) := by
    intro q15 q16 q17 q18 q19
    exact ((rfl).symm).trans ((((congrArg (fun t => q19 ◇ t) ((apc18 q15 q16 q17 q18 q19).symm)).symm).trans (apc13 q15 q15 q15 q15 q15 q19 q15 q15)).trans (rfl))
  have apc48 : forall (q20 q21 q22 q23 : G), (q23 ◇ ((q22 ◇ q20) ◇ q21)) = ((q23 ◇ q23) ◇ q23) := by
    intro q20 q21 q22 q23
    exact ((rfl).symm).trans ((((congrArg (fun t => q23 ◇ t) ((h q22 q20 q21 q20 q20).symm)).symm).trans (apc47 q22 q20 q20 q20 q23)).trans (rfl))
  exact (calc
    ((x ◇ y) ◇ z) = (y ◇ ((x ◇ x) ◇ x)) := h x y z y x
    _ = ((y ◇ y) ◇ y) := ((apc48 x x x y).symm).symm
    _ = (y ◇ ((z ◇ x) ◇ w)) := (apc48 x w z y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59913_to_59688 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59913_to_59688
