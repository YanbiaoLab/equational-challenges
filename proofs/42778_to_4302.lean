-- Equation42778 → Equation4302
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ ((y ◇ z) ◇ z))
-- Conclusion: x ◇ (x ◇ y) = z ◇ (x ◇ w)
-- Original submission SHA-256: 1e834913fa3962cd98bc2cc4a15a210193a690a8f02214cb96c212ce070783c3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ ((y ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ (x ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), (y ◇ (x ◇ ((y ◇ z) ◇ z))) = (y ◇ (x ◇ ((y ◇ x) ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have p1 : forall (x y z:G), (y ◇ (x ◇ ((y ◇ x) ◇ x))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (p0 x y x)).symm
  have p2 : forall (q0 q1 q2:G), (q2 ◇ ((q2 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h (q2 ◇ ((q1 ◇ q0) ◇ q0)) q1 q0).symm)).symm).trans ((h q1 q2 ((q1 ◇ q0) ◇ q0)).symm)
  have p3 : forall (q0 q1 q2:G), (q2 ◇ (((q1 ◇ ((q2 ◇ q0) ◇ q0)) ◇ q2) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) ((h (q1 ◇ ((q2 ◇ q0) ◇ q0)) q2 q0).symm))).symm).trans (p2 ((q2 ◇ q0) ◇ q0) q1 q2)
  have p4 : forall (q0 q1 q2:G), (q2 ◇ ((((q2 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ q2) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) ((h (q2 ◇ ((q1 ◇ q0) ◇ q0)) q1 q0).symm)))).symm).trans (p3 ((q1 ◇ q0) ◇ q0) q1 q2)
  have p5 : forall (q0 q1:G), (((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ t) (p4 q0 q1 q1)).symm).trans ((h q1 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) q1).symm)).trans (p2 q0 q1 q1)
  have p6 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ ((q1 ◇ q3) ◇ ((q3 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ ((q3 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)) (p2 q0 q1 q3)))).symm).trans ((h q2 q3 ((q3 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)).symm)
  have p7 : forall (q1 q3 q2 q0:G), ((q1 ◇ q1) ◇ (q3 ◇ (q1 ◇ q1))) = (q3 ◇ (q1 ◇ q1)):=by
    intro q1 q3 q2 q0
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q3 ◇ t) (p2 q2 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) (q1 ◇ q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q3 ◇ t) (p5 q0 q1)))).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ ((((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ q2) ◇ q2)) ◇ ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1))) (p5 q0 q1)))).symm).trans (p6 q2 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) q3 (q1 ◇ q1)))
  have p8 : forall (q1 q0:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q1 q0
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (p5 q0 q1)).symm).trans (p7 q1 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) q0 q0)).trans (p5 q0 q1)
  have p9 : forall (q0 q1:G), (q1 ◇ ((q1 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p7 q0 (q1 ◇ (q0 ◇ q0)) q0 q0)).symm).trans ((h (q0 ◇ q0) q1 (q0 ◇ q0)).symm)
  have pa : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p9 q0 q1)).symm).trans ((h q1 q1 (q0 ◇ q0)).symm)
  have pb : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (pa q0 q0)).symm).trans ((h q0 q0 q0).symm)
  have pc : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((p8 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1))).symm).trans (((pa q0 (q1 ◇ q1)).symm).trans (p7 q1 (q0 ◇ q0) q0 q0))).symm
  have pd : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (pc q1 q1))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pc q1 q1))).trans (pc q0 q1)).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (pc q0 q1)))).symm).trans (p1 (q1 ◇ q1) (q0 ◇ q0) q0)).trans (pc q1 q0))
  have pe : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pd q0 q1)).symm).trans (pb q1)
  have pf : forall (q1 q2 q0:G), (q2 ◇ q2) = (q1 ◇ q2):=by
    intro q1 q2 q0
    exact (((((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q0))) (pe q0 q2)))).trans (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (pe q0 q2))))).trans (cg (fun t => q2 ◇ t) (pe (q2 ◇ q2) q1))).trans (pe q1 q2)).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (pe q0 (q2 ◇ (q0 ◇ q0))))).symm).trans ((h q1 q2 (q0 ◇ q0)).symm))
  have pg : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact (((pf q0 q2 q0).symm).trans (pd q1 q2)).symm
  exact ((pg x (x ◇ (x ◇ y)) (x ◇ y)).symm).trans (pg z (x ◇ (x ◇ y)) (x ◇ w))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42778_to_4302 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42778_to_4302
