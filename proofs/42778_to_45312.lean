-- Equation42778 → Equation45312
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ ((y ◇ z) ◇ z))
-- Conclusion: x ◇ y = x ◇ (((y ◇ z) ◇ w) ◇ w)
-- Original submission SHA-256: 644248bca4738dbc6de606e0bd07166a024e5ca6e1705ddd5e83379077275a62
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (((y ◇ z) ◇ w) ◇ w)
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
  have p1 : forall (q0 q1:G), (q1 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((p0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have p2 : forall (q0 q1 q2:G), (q2 ◇ ((q2 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h (q2 ◇ ((q1 ◇ q0) ◇ q0)) q1 q0).symm)).symm).trans ((h q1 q2 ((q1 ◇ q0) ◇ q0)).symm)
  have p3 : forall (q0 q1 q2:G), (q2 ◇ (((q1 ◇ ((q2 ◇ q0) ◇ q0)) ◇ q2) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) ((h (q1 ◇ ((q2 ◇ q0) ◇ q0)) q2 q0).symm))).symm).trans (p2 ((q2 ◇ q0) ◇ q0) q1 q2)
  have p4 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ ((q0 ◇ q3) ◇ (q0 ◇ ((q3 ◇ q1) ◇ q1))))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q0 ◇ ((q3 ◇ q1) ◇ q1))) ((h q0 q3 q1).symm)))).symm).trans ((h q2 q3 (q0 ◇ ((q3 ◇ q1) ◇ q1))).symm)
  have p5 : forall (q0 q1 q2:G), (q2 ◇ ((((q2 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ q2) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q2) ((h (q2 ◇ ((q1 ◇ q0) ◇ q0)) q1 q0).symm)))).symm).trans (p3 ((q1 ◇ q0) ◇ q0) q1 q2)
  have p6 : forall (q0 q1:G), (((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ t) (p5 q0 q1 q1)).symm).trans ((h q1 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) q1).symm)).trans (p2 q0 q1 q1)
  have p7 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ ((q1 ◇ q3) ◇ ((q3 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ ((q3 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)) (p2 q0 q1 q3)))).symm).trans ((h q2 q3 ((q3 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1)).symm)
  have p8 : forall (q1 q3 q2 q0:G), ((q1 ◇ q1) ◇ (q3 ◇ (q1 ◇ q1))) = (q3 ◇ (q1 ◇ q1)):=by
    intro q1 q3 q2 q0
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q3 ◇ t) (p2 q2 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) (q1 ◇ q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q3 ◇ t) (p6 q0 q1)))).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ ((((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) ◇ q2) ◇ q2)) ◇ ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1))) (p6 q0 q1)))).symm).trans (p7 q2 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) q3 (q1 ◇ q1)))
  have p9 : forall (q1 q0:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q1 q0
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (p6 q0 q1)).symm).trans (p8 q1 ((q1 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q1) q0 q0)).trans (p6 q0 q1)
  have pa : forall (q0 q1:G), (q1 ◇ ((q1 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p8 q0 (q1 ◇ (q0 ◇ q0)) q0 q0)).symm).trans ((h (q0 ◇ q0) q1 (q0 ◇ q0)).symm)
  have pb : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pa q0 q1)).symm).trans ((h q1 q1 (q0 ◇ q0)).symm)
  have pc : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (pb q0 q0)).symm).trans ((h q0 q0 q0).symm)
  have pd : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q0 ◇ q0))) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (p9 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pb q0 q0)))).symm).trans (p4 q0 q0 q1 q0))
  have pe : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((p9 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1))).symm).trans (((pb q0 (q1 ◇ q1)).symm).trans (p8 q1 (q0 ◇ q0) q0 q0))).symm
  have pf : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (pe q1 q1))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pe q1 q1))).trans (pe q0 q1)).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (pe q0 q1)))).symm).trans (p1 (q1 ◇ q1) (q0 ◇ q0))).trans (pe q1 q0))
  have pg : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pf q0 q1)).symm).trans (pc q1)
  have ph : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => q0 ◇ t) (pg q0 q1)).trans (pg q1 q0)).symm).trans (pd q0 q1)).symm
  have pi : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact (((((cg (fun t => t ◇ (q0 ◇ ((q1 ◇ q2) ◇ q2))) (cg (fun t => q0 ◇ t) (ph q2 (q1 ◇ q2)))).trans (cg (fun t => (q0 ◇ (q2 ◇ q2)) ◇ t) (cg (fun t => q0 ◇ t) (ph q2 (q1 ◇ q2))))).trans (cg (fun t => t ◇ (q0 ◇ (q2 ◇ q2))) (pg q2 q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pg q2 q0))).symm).trans (((ph (q0 ◇ ((q1 ◇ q2) ◇ q2)) q1).symm).trans ((h q0 q1 q2).symm))
  exact ((pi x y (x ◇ y)).symm).trans (pi x (((y ◇ z) ◇ w) ◇ w) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42778_to_45312 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42778_to_45312
