-- Equation34895 → Equation55012
-- Recorded verdict: true
-- Premise: x = ((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x
-- Conclusion: x ◇ (y ◇ x) = z ◇ ((w ◇ x) ◇ x)
-- Original submission SHA-256: e34a4385fb150015cb95f1a1d0cb077da9ed46269d096030ec03e953572c8935
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = z ◇ ((w ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), (((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x) = (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (x y z:G), (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (p0 x x x)).symm
  have p2 : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ (q3 ◇ q3)) ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) = ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q3) ((h q3 q0 q1).symm)))).symm).trans ((h ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) q2 q3).symm)
  have p3 : forall (q0 q1:G), (((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) = ((q1 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q0)) (p2 ((q1 ◇ q0) ◇ q0) q0 q1 q1)).symm).trans ((h ((q1 ◇ q0) ◇ q0) (q1 ◇ q1) ((q1 ◇ q0) ◇ q0)).symm)
  have p4 : forall (q0:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ q0)) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (p1 q0 (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0)))))).trans (cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ q0)) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ q0) (p1 q0 (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0)))))).trans (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ q0) (p1 q0 (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0))))).symm).trans ((((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ q0)) (cg (fun t => t ◇ q0) (p1 q0 q0 q0))))).symm).trans (p3 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))).trans (cg (fun t => t ◇ q0) (p1 q0 (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0))))
  have p5 : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => (q1 ◇ q1) ◇ t) (p4 q0))).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 (q0 ◇ q0)).symm)
  have p6 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) = ((q1 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) (cg (fun t => (q2 ◇ q2) ◇ t) (p5 q0 q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p5 q0 q1)))).symm).trans ((h ((q1 ◇ q1) ◇ (q0 ◇ q0)) q2 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm))
  have p7 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => (q2 ◇ q2) ◇ t) (p6 q0 q0 q1))).symm).trans ((h (q1 ◇ q1) q2 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)
  have p8 : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (p5 q0 q0)).symm).trans (p7 q0 q1 (q0 ◇ q0))
  have p9 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (p8 q0 q0)).symm).trans (p4 q0)
  have pa : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (p9 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans (p8 q0 q1)
  have pb : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1))) = ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1))) (p7 q0 q2 (q0 ◇ q0))).symm).trans (p2 q0 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q2)
  have pc : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ ((((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) ◇ q3) ◇ q3)) = (q3 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((((cg (fun t => (((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) ◇ t) (pa q2 q3)).trans (pa ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) q3)).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q3) ((h q3 q0 q1).symm)))).symm).trans (pb q2 q3 ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))))).symm
  have pd : forall (q0 q1 q2 q3:G), ((((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)) ◇ q2) ◇ q2) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)) ◇ q2) ◇ q2)) (pa q3 q2)).trans (pc q0 q1 q2 q2)).symm).trans (((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)) ◇ q2) ◇ q2)) (cg (fun t => (q3 ◇ q3) ◇ t) (pc q0 q1 ((((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)) ◇ q2) ◇ q2) q2))).symm).trans ((h ((((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)) ◇ q2) ◇ q2) q3 ((((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)) ◇ q2) ◇ q2)).symm))).symm
  have pe : forall (q0 q1 q2:G), ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0))) = ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0))) (pa ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0))).symm).trans ((((cg (fun t => ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (p3 q0 q1))).symm).trans (pb q2 ((q1 ◇ q0) ◇ q0) (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)))).trans (cg (fun t => (q2 ◇ q2) ◇ t) (p3 q0 q1)))
  have pf : forall (q0 q1:G), ((((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) = ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => (((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) ◇ t) (pb ((q1 ◇ q0) ◇ q0) q0 q1)).symm).trans (pe ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0) q1)).trans (pb ((q1 ◇ q0) ◇ q0) q0 q1)
  have pg : forall (q0 q1:G), (((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) = ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) (pf q0 q1)).symm).trans (p3 ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0))
  have ph : forall (q0 q1 q2 q3:G), ((((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q2 ◇ q3) ◇ q3)) ◇ q2) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q2 ◇ q3) ◇ q3)) (pg q0 q1))).symm).trans ((h q2 ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) q3).symm)
  have pi : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q0) (ph q1 q0 ((q0 ◇ q1) ◇ q1) ((q0 ◇ q1) ◇ q1))).symm).trans ((h q0 ((((q0 ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q1) ◇ q1)) q1).symm)
  have pj : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (pi q0 q0)).symm).trans (pi (q0 ◇ q0) q0)
  have pk : forall (q1 q0:G), (q1 ◇ q1) = q1:=by
    intro q1 q0
    exact (((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (cg (fun t => (q0 ◇ q0) ◇ t) (pa q1 q1)))).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pa q0 q1)))).trans (pi q1 q1)).symm).trans (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (pj q1))))).symm).trans (pd q0 (q1 ◇ q1) q1 q0))).symm
  have pl : forall (q0 q1:G), (q0 ◇ q1) = q1:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) (pk q0 (q0 ◇ q0))).trans (cg (fun t => q0 ◇ t) (pk q1 (q1 ◇ q1)))).symm).trans ((pa q0 q1).trans (pk q1 (q1 ◇ q1)))
  exact (calc
    (x ◇ (y ◇ x)) = x:=(cg (fun t => x ◇ t) (pl y x)).trans (pl x x)
    _ = (z ◇ ((w ◇ x) ◇ x)):=(((cg (fun t => z ◇ t) (cg (fun t => t ◇ x) (pl w x))).trans (cg (fun t => z ◇ t) (pl x x))).trans (pl z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34895_to_55012 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34895_to_55012
