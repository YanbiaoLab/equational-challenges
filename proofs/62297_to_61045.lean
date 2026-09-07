-- Equation62297 → Equation61045
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = ((y ◇ x) ◇ w) ◇ w
-- Conclusion: (x ◇ y) ◇ x = (x ◇ (y ◇ z)) ◇ w
-- Original submission SHA-256: ad3921f6a21365fa20a1f3b02a05b6f2b24661f570d903947041b53515b60589
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((y ◇ x) ◇ w) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = (x ◇ (y ◇ z)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (x y z w:G), ((x ◇ y) ◇ z) = ((x ◇ y) ◇ x):=by
    intro x y z w
    exact (h x y z x).trans ((h x y x x).symm)
  have p1 : forall (x y z w:G), (((y ◇ x) ◇ x) ◇ x) = (((y ◇ x) ◇ w) ◇ w):=by
    intro x y z w
    exact (((h x y x w).symm).trans (h x y x x)).symm
  have p2 : forall (q0 q1 q3 q2 q4:G), ((q3 ◇ (q1 ◇ q0)) ◇ q3) = (((q0 ◇ q1) ◇ q0) ◇ q3):=by
    intro q0 q1 q3 q2 q4
    exact (((congrArg (fun t => t ◇ q3) (p0 q0 q1 q2 ((q0 ◇ q1) ◇ q2))).symm).trans ((((congrArg (fun t => t ◇ q3) ((h q0 q1 q2 q3).symm)).symm).trans ((h q3 (q1 ◇ q0) q4 q3).symm)).trans (p0 q3 (q1 ◇ q0) q4 ((q3 ◇ (q1 ◇ q0)) ◇ q4)))).symm
  have p3 : forall (x y z w:G), (((y ◇ x) ◇ w) ◇ w) = ((x ◇ y) ◇ x):=by
    intro x y z w
    exact (((p0 x y x ((x ◇ y) ◇ x)).symm).trans (h x y x w)).symm
  have p4 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ q2) ◇ q0) = ((q1 ◇ q2) ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q0) (p0 q2 q1 q0 q0)).symm).trans ((h q1 q2 q3 q0).symm)).trans (p0 q1 q2 q3 ((q1 ◇ q2) ◇ q3))
  have p5 : forall (q0 q1 q3 q2:G), ((q1 ◇ q0) ◇ q1) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1 q3 q2
    exact (((congrArg (fun t => t ◇ q3) (p0 q0 q1 q2 ((q0 ◇ q1) ◇ q2))).trans (p4 q3 q1 q0 (((q0 ◇ q1) ◇ q0) ◇ q3))).symm).trans ((((congrArg (fun t => t ◇ q3) ((h q0 q1 q2 (q1 ◇ q0)).symm)).symm).trans (p4 q3 (q1 ◇ q0) (q1 ◇ q0) q0)).trans ((congrArg (fun t => t ◇ (q1 ◇ q0)) (p0 q1 q0 (q1 ◇ q0) ((q1 ◇ q0) ◇ (q1 ◇ q0)))).trans (p4 (q1 ◇ q0) q0 q1 (((q1 ◇ q0) ◇ q1) ◇ (q1 ◇ q0)))))
  have p6 : forall (q0 q1 q2:G), (((q1 ◇ q2) ◇ q1) ◇ q0) = ((q1 ◇ q2) ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) (p5 q1 q2 ((q2 ◇ q1) ◇ q2) ((q2 ◇ q1) ◇ q2))).symm).trans ((((congrArg (fun t => t ◇ q0) (p0 q2 q1 q0 q0)).symm).trans ((p1 q1 q2 q0 q0).symm)).trans (p3 q1 q2 (((q2 ◇ q1) ◇ q1) ◇ q1) q1))
  have p7 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ q0) = ((q1 ◇ q2) ◇ q1):=by
    intro q0 q1 q2
    exact (h q2 q1 q0 q1).trans (p6 q1 q1 q2)
  have p8 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ (q1 ◇ q0)) ◇ q3) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((p2 q0 q1 q3 q2 q4).trans (p4 q3 q1 q0 (((q0 ◇ q1) ◇ q0) ◇ q3))).trans (p7 q1 q0 q1)
  have p9 : forall (q0 q1 q2 q3:G), ((q2 ◇ q3) ◇ q2) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((p6 (q0 ◇ q1) q0 q1).symm).trans (((congrArg (fun t => t ◇ (q0 ◇ q1)) (p0 q0 q1 (q3 ◇ q2) q0)).symm).trans (p8 q2 q3 q0 (q0 ◇ q1) q0))).symm
  exact (calc
    ((x ◇ y) ◇ x) = (((x ◇ y) ◇ x) ◇ (y ◇ z)):=(p6 (y ◇ z) x y).symm
    _ = ((((y ◇ z) ◇ x) ◇ (y ◇ z)) ◇ (y ◇ z)):=(congrArg (fun t => t ◇ (y ◇ z)) (p9 x y (y ◇ z) x)).symm
    _ = ((x ◇ (y ◇ z)) ◇ w):=(h x (y ◇ z) w (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_62297_to_61045 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_62297_to_61045
