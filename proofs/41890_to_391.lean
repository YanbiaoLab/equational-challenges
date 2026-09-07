-- Equation41890 → Equation391
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
-- Conclusion: x ◇ y = (y ◇ z) ◇ y
-- Original submission SHA-256: 981de19420f6e2f7a7cc7220d6a073bce254460623fdfdc164a5d14951e5d8cc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) ((h q1 q1 q0).symm)).symm).trans ((h q1 (q0 ◇ q1) q1).symm)
  have p1 : forall (x y z:G), (y ◇ (x ◇ (x ◇ (z ◇ y)))) = (y ◇ (x ◇ (x ◇ (x ◇ y)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have p2 : forall (x y z:G), (y ◇ (x ◇ (x ◇ (x ◇ y)))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (p1 x y x)).symm
  have p3 : forall (q0 q1 q2:G), ((q2 ◇ (q0 ◇ q1)) ◇ (q1 ◇ (q2 ◇ q1))) = (q1 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q2 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q1 ◇ t) ((h q2 q1 q0).symm))).symm).trans ((h q1 (q2 ◇ (q0 ◇ q1)) q2).symm)
  have p4 : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p0 q0 q1))).symm).trans ((h (q0 ◇ q1) q1 q1).symm)
  have p5 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p0 q1 q1)).trans (p3 q0 q1 q1)).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (p0 q0 q1)).symm).trans (p0 (q0 ◇ q1) (q1 ◇ q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (p0 q0 q1)))).symm
  have p6 : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0
    exact (((p2 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))).symm).trans (((cg (fun t => q0 ◇ t) (p5 q0 q0)).symm).trans (p4 q0 q0))).symm
  have p7 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p6 q1)))).symm).trans ((h q0 q1 (q1 ◇ q1)).symm)
  have p8 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => t ◇ (q0 ◇ q0)) (p0 q0 q0)).symm).trans (p6 (q0 ◇ q0))).trans (p0 q0 q0)
  have p9 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q0 ◇ q1))))) = (q2 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p0 q0 q1)))).symm).trans ((h q2 (q1 ◇ q1) (q0 ◇ q1)).symm)
  have pa : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p2 q0 q1 q0)))).symm).trans (p2 q1 (q0 ◇ (q0 ◇ (q0 ◇ q1))) q0)).trans (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))
  have pb : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = ((q1 ◇ q1) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) (p0 q1 q1)).trans (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p5 q0 q1))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p0 q0 q1))).symm).trans (p5 (q0 ◇ q1) (q1 ◇ q1))).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p0 q0 q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (p5 q0 q1))))
  have pc : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q0) = (q0 ◇ ((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (p0 (q1 ◇ q0) (q1 ◇ q0))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (p6 (q1 ◇ q0)))).symm).trans ((h ((q1 ◇ q0) ◇ (q1 ◇ q0)) q0 q1).symm))).symm
  have pd : forall (q0 q1 q2 q3:G), ((q0 ◇ (q0 ◇ (q1 ◇ q3))) ◇ (q2 ◇ (q2 ◇ (q0 ◇ q3)))) = (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q3)))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q3))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q0 q3 q1).symm)))).symm).trans ((h q2 (q0 ◇ (q0 ◇ (q1 ◇ q3))) q3).symm)
  have pe : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (p3 q1 q1 q1)).trans (pd q1 q0 q1 q1)).symm).trans ((((cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p8 q1))).symm).trans (pd q1 q0 (q1 ◇ (q1 ◇ q1)) q1)).trans (pb q0 q1))).symm
  have pf : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ (q2 ◇ (q0 ◇ q1)))) ◇ (q1 ◇ q1)) = (q1 ◇ (q1 ◇ (q1 ◇ (q2 ◇ (q0 ◇ q1))))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ (q1 ◇ (q2 ◇ (q0 ◇ q1)))) ◇ t) ((h q1 q1 q0).symm)).symm).trans (pd q1 q2 q1 (q0 ◇ q1))
  have pg : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((((cg (fun t => (q0 ◇ q1) ◇ t) (pe q0 q1)).trans (p2 q1 (q0 ◇ q1) ((q0 ◇ q1) ◇ (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1))))))).symm).trans (((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p5 q0 q1))).symm).trans ((h (q1 ◇ q1) (q0 ◇ q1) q1).symm))).symm
  have ph : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q0)))) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (p5 q1 q0)).symm).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pg q1 q0))).symm).trans ((h (q0 ◇ q0) q0 q1).symm)).trans (p6 q0))
  have pi : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((((cg (fun t => (q1 ◇ q1) ◇ t) (p5 q1 (q0 ◇ q1))).trans (p9 q0 q1 (q0 ◇ q1))).trans (p0 q0 q1)).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (pg q1 (q0 ◇ q1)))).symm).trans (p9 q0 q1 ((q0 ◇ q1) ◇ (q0 ◇ q1))))).symm
  have pj : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q1) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (pg q1 (q0 ◇ q1))).trans (p4 q0 q1)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (pi q0 q1))).symm).trans ((h ((q0 ◇ q1) ◇ (q0 ◇ q1)) q1 q1).symm))).symm
  have pk : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) (p0 q1 q1)).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (p0 q0 q1)).symm).trans (pg (q0 ◇ q1) (q1 ◇ q1))).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (p0 q0 q1)).trans (p5 q0 q1)))
  have pl : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))) = (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))):=by
    intro q0 q1 q2
    exact ((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (p5 q0 q2)).trans (pd q0 q1 q2 q2)).symm).trans (((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (pg q0 q2))).symm).trans (pd q0 q1 (q2 ◇ q2) q2))).symm
  have pm : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q0 ◇ q1))))) = (q2 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (pg q0 q1)))).symm).trans ((h q2 (q0 ◇ q1) (q1 ◇ q1)).symm)
  have pn : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) (cg (fun t => (q1 ◇ q1) ◇ t) (ph q1 q0))).trans (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) (p0 q1 q1))).symm).trans ((((cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1))))) (ph q1 q0))).symm).trans (pc (q1 ◇ (q1 ◇ (q0 ◇ q1))) q1)).trans (((((((cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1))))) (ph q1 q0)))).trans (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (ph q1 q0))))).trans (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) ◇ t) (p0 q1 q1)))).trans (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ q1))) (ph q1 q0)))).trans (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (p5 q1 q1))).trans (pd q1 q0 q1 q1)).trans (ph q1 q0)))
  have po : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p0 q0 q1))).symm).trans (pl (q0 ◇ q1) q1 q1)).trans ((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p0 q0 q1))).trans (p4 q0 q1))
  have pp : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) ◇ (q0 ◇ q1)) = ((q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q0 ◇ q1)) (pd q0 q0 q0 q1)).symm).trans ((((cg (fun t => ((q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) ◇ t) (p2 q0 q1 q0)).symm).trans (pg q1 (q0 ◇ (q0 ◇ (q0 ◇ q1))))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))))
  have pq : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((((((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ ((q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) ◇ (q1 ◇ (q0 ◇ q1)))) (cg (fun t => q1 ◇ t) (ph q1 q0)))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) (ph q1 q0))))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p5 q0 q1)))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (pn q0 q1))).trans (p0 q0 q1)).symm).trans ((((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1))))) ◇ t) (pp q1 (q0 ◇ q1)))).symm).trans (pm q0 q1 (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1))))))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => q1 ◇ t) (ph q1 q0))))).symm
  have pr : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) = ((q0 ◇ q2) ◇ ((q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) ((h q0 q2 q1).symm)).symm).trans (p0 q2 (q0 ◇ (q0 ◇ (q1 ◇ q2))))).symm
  have ps : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ (q0 ◇ q1)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (p2 q0 q1 q0)).symm).trans (pr q0 q0 q1)).trans ((cg (fun t => (q0 ◇ q1) ◇ t) (pd q0 q0 q0 q1)).trans (p2 q0 (q0 ◇ q1) ((q0 ◇ q1) ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))))
  have pt : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) ◇ (q0 ◇ q1)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (pp q0 q1).trans (ps q0 q1)
  have pu : forall (q0 q1:G), ((q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q0)))) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => q0 ◇ t) (ps q1 (q1 ◇ q0))).trans (p2 q1 q0 (q0 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q0)))))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q0)))) ◇ t) (pt q1 q0))).symm).trans ((h (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q0)))) q0 q1).symm))).symm
  have pv : forall (q0 q1 q2:G), ((q2 ◇ (q2 ◇ q2)) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))) = (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))):=by
    intro q0 q1 q2
    exact ((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (pk q0 q2)).trans (pd q0 q1 q2 q2)).symm).trans (((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => (q2 ◇ (q2 ◇ q2)) ◇ t) (pq q0 q2))).symm).trans (pd q0 q1 (q2 ◇ (q2 ◇ q2)) q2))).symm
  have pw : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q0 ◇ q1))))) = (q2 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q1 ◇ (q0 ◇ q1))))) (p0 q1 q1)).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p0 q0 q1)))).symm).trans (pl q2 (q0 ◇ q1) (q1 ◇ q1))).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p0 q0 q1)))).trans (p9 q0 q1 q2)))
  have px : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((((((((cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p2 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))))))).trans (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (p3 q0 q0 q0)))).trans (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ q0)))) (pv q0 q0 q0))).trans (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ q0)))) (p2 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))))).trans (pl q1 q0 q0)).trans (p7 q1 q0)).symm).trans ((((cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (pv q0 q0 q0)))).symm).trans (pw q0 (q0 ◇ (q0 ◇ q0)) q1)).trans (cg (fun t => q1 ◇ t) (p3 q0 q0 q0)))).symm
  have py : forall (q0 q1:G), ((q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((px q1 (q1 ◇ (q1 ◇ (q0 ◇ q1)))).symm).trans (pd q1 q0 q1 q1)).trans (ph q1 q0)
  have pz : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ q0)) = (q0 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (((((cg (fun t => (q1 ◇ q0) ◇ t) (pd q0 q0 q0 q0)).trans (cg (fun t => (q1 ◇ q0) ◇ t) (p2 q0 q0 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))))).trans (p0 q1 q0)).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))) (px q0 q1)).symm).trans (p0 q1 (q0 ◇ (q0 ◇ (q0 ◇ q0))))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (px q0 q1)))).symm
  have p10 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q0 ◇ (q0 ◇ q1))) = (q0 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => q0 ◇ t) (px q1 q0))).symm).trans ((h q0 (q1 ◇ (q1 ◇ q1)) q1).symm)
  have p11 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ (q0 ◇ q1))) = (q0 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q1))) (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p3 q1 q1 q1))).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q1))) (pv q1 q1 q1))).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q1))) (p2 q1 q1 (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1))))))).symm).trans ((((cg (fun t => ((q1 ◇ (q1 ◇ q1)) ◇ ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1)))) ◇ t) (cg (fun t => q0 ◇ t) (px q1 q0))).symm).trans (pv q0 q1 (q1 ◇ (q1 ◇ q1)))).trans ((cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => q0 ◇ t) (px q1 q0))).trans (p10 q0 q1)))
  have p12 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0))))) = (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0))))):=by
    intro q0 q1
    exact ((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ t) (p6 q0)).trans (pf q0 q0 q1)).symm).trans (((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ t) (po q0 q0)).symm).trans (pd q0 q1 (q0 ◇ q0) (q0 ◇ q0)))).symm
  have p13 : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0))))) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((p12 q0 q1).symm).trans ((h q0 (q0 ◇ q0) q1).symm)
  have p14 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ (q0 ◇ (q1 ◇ q1)))) = (q1 ◇ (q1 ◇ (q0 ◇ (q1 ◇ q1)))):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q1 ◇ q1)))) (p2 q1 q1 (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))))).symm).trans (((cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q1 ◇ q1)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p13 q1 q0)))).symm).trans (pu (q1 ◇ (q0 ◇ (q1 ◇ q1))) q1))
  have p15 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) = (q2 ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) (ph q2 q0)).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q0 q2 q1).symm))))).symm).trans (pt q2 (q0 ◇ (q0 ◇ (q1 ◇ q2)))))
  have p16 : forall (q0 q1 q2:G), (q2 ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) = (q2 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact (((pg q0 q2).symm).trans (((cg (fun t => (q2 ◇ q2) ◇ t) ((h q0 q2 q1).symm)).symm).trans (p15 q0 q1 q2))).symm
  have p17 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2))))) = (q2 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact (p15 q0 q1 q2).trans (p16 q0 q1 q2)
  have p18 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q1))))) ◇ q1) = (q1 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q1)))):=by
    intro q0 q1 q2
    exact (((cg (fun t => q1 ◇ t) (pt q0 (q2 ◇ q1))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q1))))) ◇ t) (pu (q2 ◇ q1) q0))).symm).trans ((h (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ q1))))) q1 q2).symm))).symm
  have p19 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (ph q0 q1)).trans (p11 q1 q0)).symm).trans ((((cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p2 q1 q0 q0))))).symm).trans (p18 q0 (q1 ◇ (q1 ◇ q0)) q1)).trans ((cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p2 q1 q0 (q0 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q0))))))).trans (p3 q1 q0 q1)))
  have p1a : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q2 ◇ (q0 ◇ q1))) = (q1 ◇ (q2 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (ph q1 q2)).symm).trans ((((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) ((h q2 q1 q0).symm))))).symm).trans (p18 q1 (q2 ◇ (q0 ◇ q1)) q2)).trans ((cg (fun t => (q2 ◇ (q0 ◇ q1)) ◇ t) (p16 q2 q0 q1)).trans (p3 q0 q1 q2)))
  have p1b : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))) = (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (pa q0 q1)))).symm).trans ((h q2 (q1 ◇ (q1 ◇ (q0 ◇ q1))) (q0 ◇ (q0 ◇ (q0 ◇ q1)))).symm)
  have p1c : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = (q1 ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))):=by
    intro q0 q1 q2
    exact ((((((cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))) (ph (q1 ◇ (q1 ◇ (q0 ◇ q1))) q2)).trans (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))) (p1b q0 q1 q1))).trans (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))) (ph q1 q0))).trans (pl q2 q0 q1)).symm).trans ((((cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))) (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (p1b q0 q1 q2))))).symm).trans (pu (q2 ◇ (q2 ◇ (q0 ◇ q1))) (q1 ◇ (q1 ◇ (q0 ◇ q1))))).trans (p1b q0 q1 q2))).symm
  have p1d : forall (q0 q1:G), ((q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) (ph q1 q0)).trans (p1a q0 q1 q1)).symm).trans (((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) (p1b q0 q1 q1)).symm).trans (pj q1 (q1 ◇ (q0 ◇ q1))))).symm
  have p1e : forall (q0 q1:G), (q0 ◇ ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ (q1 ◇ (q1 ◇ q0)))) = ((q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q0))) ◇ t) (ps q1 q0))).symm).trans ((h (q1 ◇ (q1 ◇ (q1 ◇ q0))) q0 q1).symm)
  have p1f : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q1 ◇ t) (p7 q0 q1)))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q1))) ◇ t) (p1d q0 q1))).trans (pd q0 q1 q1 q1)).trans (p7 q0 q1)).symm).trans ((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q1))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p7 q0 q1))))).symm).trans (p1e (q0 ◇ (q0 ◇ (q1 ◇ q1))) q1)).trans ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p7 q0 q1)))).trans (pd q1 q0 q0 q1)))).symm
  have p1g : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (ps q0 q1))).trans (p1e q1 q0)).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (p2 q0 q1 q0)))).symm).trans (p1f q1 (q0 ◇ (q0 ◇ (q0 ◇ q1))))).trans (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1))))))
  have p1h : forall (q0 q1:G), ((q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((((((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q1 ◇ t) (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (p1d q0 q1))).trans (pd q0 q0 q1 q1)).trans (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))).symm).trans ((((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p2 q0 q1 q0))))).symm).trans (p1e (q0 ◇ (q0 ◇ (q0 ◇ q1))) q1)).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))))))).symm
  have p1i : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = ((q1 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((((((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p1c q0 q0 q1)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p7 q1 q0))))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ q0))) (p1c q0 q0 q1)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ q0))) (p7 q1 q0)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (pz q0 q1)))).trans (po q1 q0)).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) ◇ ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0))))))) (p1h q0 q0)).symm).trans (po q1 (q0 ◇ (q0 ◇ (q0 ◇ q0))))).trans ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) (p1c q0 q0 q1)).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) (p7 q1 q0))))).symm
  have p1j : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1))) = ((q0 ◇ q1) ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1))) (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p3 q1 q1 q1))).trans (cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1))) (pv q1 q1 q1))).trans (cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1))) (p2 q1 q1 (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1))))))).trans (p1a (q0 ◇ q1) q1 (q0 ◇ q1))).symm).trans ((((cg (fun t => ((q1 ◇ (q1 ◇ q1)) ◇ ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1)))) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p1i q1 q0))).symm).trans (pv (q0 ◇ q1) q1 (q1 ◇ (q1 ◇ q1)))).trans ((cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p1i q1 q0))).trans (p10 (q0 ◇ q1) q1)))
  have p1k : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q2 ◇ (q1 ◇ q0))) = (q0 ◇ (q2 ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2
    exact ((((((cg (fun t => ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ q0) ◇ t) (cg (fun t => q2 ◇ t) (p1c q0 q0 q1))).trans (cg (fun t => ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ q0) ◇ t) (cg (fun t => q2 ◇ t) (p7 q1 q0)))).trans (cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (py q0 q0))).trans (p1a q1 q0 q2)).symm).trans ((((cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))))) (px q0 (q0 ◇ (q0 ◇ (q0 ◇ q0))))).symm).trans (p1a q1 (q0 ◇ (q0 ◇ (q0 ◇ q0))) q2)).trans ((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q2 ◇ t) (p1c q0 q0 q1))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q2 ◇ t) (p7 q1 q0)))))).symm
  have p1l : forall (q0 q1 q2:G), ((q2 ◇ (q2 ◇ (q0 ◇ q2))) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))) = (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))):=by
    intro q0 q1 q2
    exact (((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => (q2 ◇ (q2 ◇ (q0 ◇ q2))) ◇ t) (p16 q0 q1 q2))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (p1d q0 q2))).trans (pd q0 q1 q2 q2)).symm).trans ((((cg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))))) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q0 q2 q1).symm))))).symm).trans (p1e (q0 ◇ (q0 ◇ (q1 ◇ q2))) q2)).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q1 ◇ q2)))) (cg (fun t => q2 ◇ t) (p16 q0 q1 q2))))).symm
  have p1m : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ ((q1 ◇ (q0 ◇ q2)) ◇ (q2 ◇ (q1 ◇ (q0 ◇ q2))))) = ((q1 ◇ (q0 ◇ q2)) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ q2) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q2)) ◇ t) (p3 q0 q2 q1))).symm).trans ((h (q1 ◇ (q0 ◇ q2)) (q1 ◇ q2) q2).symm)
  have p1n : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)) = (q1 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)):=by
    intro q0 q1
    exact (((p17 (q1 ◇ (q0 ◇ q1)) q0 q1).symm).trans (((cg (fun t => (q1 ◇ q1) ◇ t) (p1c q0 q1 (q1 ◇ (q0 ◇ q1)))).symm).trans (p1m q0 q1 q1))).symm
  have p1o : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p0 q0 q1))).symm).trans (pv (q0 ◇ q1) q1 q1)).trans ((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p0 q0 q1))).trans (p4 q0 q1))
  have p1p : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ (q1 ◇ q2))))) ◇ (q2 ◇ q2)) = (q0 ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact ((((cg (fun t => (q2 ◇ q2) ◇ t) (ps q0 (q2 ◇ (q1 ◇ q2)))).trans (p9 q1 q2 q0)).symm).trans (((cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ (q1 ◇ q2))))) ◇ t) (p1g q0 (q2 ◇ (q1 ◇ q2))))).symm).trans (p9 q1 q2 (q0 ◇ (q0 ◇ (q0 ◇ (q2 ◇ (q1 ◇ q2)))))))).symm
  have p1q : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q2 ◇ (q2 ◇ (q0 ◇ (q1 ◇ q1))))) = (q2 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p1p q0 q0 q1)))).symm).trans ((h q2 (q1 ◇ q1) (q0 ◇ (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q1)))))).symm)
  have p1r : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ (q2 ◇ (q0 ◇ (q1 ◇ q1))))) = (q2 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((((cg (fun t => (q2 ◇ (q2 ◇ (q0 ◇ (q1 ◇ q1)))) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p1a q1 q1 q2))).trans (cg (fun t => (q2 ◇ (q2 ◇ (q0 ◇ (q1 ◇ q1)))) ◇ t) (p14 q2 q1))).trans (pd q2 q0 q1 (q1 ◇ q1))).symm).trans ((((cg (fun t => (q2 ◇ (q2 ◇ (q0 ◇ (q1 ◇ q1)))) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p1q q0 q1 q2)))).symm).trans (p2 (q1 ◇ q1) (q2 ◇ (q2 ◇ (q0 ◇ (q1 ◇ q1)))) q0)).trans (p1q q0 q1 q2))
  have p1s : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q0 ◇ (q1 ◇ (q1 ◇ q0))))) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p0 q0 q0)))).trans (cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (p19 q0 q1)))).symm).trans (((cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p6 (q0 ◇ q0))))).symm).trans (p1r ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0 q1))
  have p1t : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ ((q0 ◇ q1) ◇ q1))) = (q1 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q1 ◇ t) ((h (q0 ◇ q1) q1 q0).symm))).symm).trans (p1r (q0 ◇ q1) (q0 ◇ q1) q1)
  have p1u : forall (q0 q1 q2:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q2 ◇ (q1 ◇ (q2 ◇ (q2 ◇ (q0 ◇ q1)))))) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q2 ◇ t) (p1c q0 q1 q2))).symm).trans (((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) (p5 q0 q1)))).symm).trans ((h q2 (q1 ◇ (q0 ◇ q1)) (q1 ◇ q1)).symm))
  have p1v : forall (q0 q1 q2:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q2 ◇ (q2 ◇ q1))) = (q2 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q2 ◇ t) ((h q2 q1 q0).symm))).symm).trans (p1u q0 q1 q2)
  have p1w : forall (q0 q1:G), (q1 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ (q0 ◇ q1)))) = ((q1 ◇ (q0 ◇ q1)) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p1v q0 q1 (q1 ◇ (q0 ◇ q1)))).symm).trans ((h (q1 ◇ (q0 ◇ q1)) q1 (q1 ◇ (q0 ◇ q1))).symm)
  have p1x : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => q1 ◇ t) (p1w q0 q1))).symm).trans ((h q1 (q1 ◇ (q0 ◇ q1)) (q1 ◇ (q0 ◇ q1))).symm)
  have p1y : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ (q1 ◇ (q2 ◇ q0)))) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (px q0 q2)))).symm).trans ((h q1 (q0 ◇ (q0 ◇ (q0 ◇ q0))) q2).symm)).trans ((p1c q0 q0 q1).trans (p7 q1 q0))
  have p1z : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q1))) ◇ t) (p1x q0 q1)).trans (p1l q1 q0 q1)).trans (ph q1 q0)).symm).trans (((cg (fun t => (q1 ◇ (q1 ◇ (q1 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p1n q0 q1))).symm).trans (p1y q1 (q1 ◇ (q0 ◇ q1)) q1))).symm
  have p20 : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ (q2 ◇ q0))) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((p1y q0 (q1 ◇ (q1 ◇ (q2 ◇ q0))) q1).symm).trans ((((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q2 ◇ q0))) ◇ t) (cg (fun t => (q1 ◇ (q1 ◇ (q2 ◇ q0))) ◇ t) (p1y q0 q1 q2)))).symm).trans (p1f (q0 ◇ (q0 ◇ (q0 ◇ q0))) (q1 ◇ (q1 ◇ (q2 ◇ q0))))).trans (p1y q0 q1 q2))
  have p21 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q1 ◇ q0))) = (q0 ◇ (q1 ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((p1v q1 q0 q1).symm).trans (((cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) (cg (fun t => q0 ◇ t) (p2 q1 q0 q0))).symm).trans (p20 (q1 ◇ (q1 ◇ q0)) q0 q1))
  have p22 : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (p1n q0 q1).trans (cg (fun t => q1 ◇ t) (p1z q0 q1))
  have p23 : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((((((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p3 q0 q1 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (pl q1 q0 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (ph q1 q0)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (p22 q0 q1))).trans (p1a q1 q1 q1)).symm).trans ((((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p22 q0 q1))))).symm).trans (p1s (q1 ◇ q1) (q1 ◇ (q0 ◇ q1)))).trans ((cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p0 q1 q1)).trans (p3 q0 q1 q1)))
  have p24 : forall (q0 q1 q2:G), (q2 ◇ (q2 ◇ (q1 ◇ q2))) = (q2 ◇ (q2 ◇ (q0 ◇ q2))):=by
    intro q0 q1 q2
    exact (((p23 q0 q2).symm).trans (p23 q1 q2)).symm
  have p25 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ (q2 ◇ (q0 ◇ q2)))) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (p24 q0 q1 q2)).symm).trans (p1f q1 q2)
  have p26 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q0 ◇ q1))) = (q1 ◇ (q2 ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact ((((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p25 q0 (q1 ◇ (q0 ◇ q1)) q1))).trans (cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p1z q0 q1)))).trans (cg (fun t => q2 ◇ t) (p22 q0 q1))).trans (p19 q1 q2)).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (pk q0 q1)))).symm).trans (p25 (q1 ◇ (q1 ◇ q1)) q2 (q1 ◇ (q0 ◇ q1))))).symm
  have p27 : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) = ((q1 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ q0) ◇ t) (pz q0 (q1 ◇ q0))).trans (p1t q1 q0)).symm).trans ((((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p1i q0 q1))).symm).trans (p21 (q0 ◇ (q0 ◇ (q0 ◇ q0))) (q1 ◇ q0))).trans (((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (p25 q0 (q1 ◇ q0) q0))).trans (p1k q0 (q1 ◇ q0) (q1 ◇ q0))).trans (p1j q1 q0)))
  have p28 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => q2 ◇ t) (p1a q0 q0 q1)).symm).trans (p26 q1 (q0 ◇ q0) q2)).trans ((pl q2 q0 q0).trans (p7 q2 q0))
  have p29 : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p1z q0 q1)))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => q1 ◇ t) (p22 q0 q1)))).trans (pz q1 q0)).symm).trans (((cg (fun t => t ◇ (q0 ◇ q1)) (p26 q0 q1 (q1 ◇ (q0 ◇ q1)))).symm).trans (pj q1 (q0 ◇ q1)))).symm
  have p2a : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ (q1 ◇ q1))) = ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p1z q0 q1)))).trans (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (cg (fun t => q1 ◇ t) (p22 q0 q1)))).trans (p1k q1 q0 (q0 ◇ q1))).trans (p27 q1 q0)).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (p26 q0 q1 (q1 ◇ (q0 ◇ q1)))).symm).trans (pi q1 (q0 ◇ q1)))
  have p2b : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => ((q1 ◇ (q1 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) ◇ t) (p3 q1 q1 q1)).trans (cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) (p1o q0 q1))).trans (p25 q1 ((q0 ◇ q1) ◇ q1) q1)).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1)))) (cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p2a q0 q1))).symm).trans (p22 (q0 ◇ q1) (q1 ◇ (q1 ◇ q1)))).trans (((cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p3 q1 q1 q1)).trans (pv q1 q1 q1)).trans (p2 q1 q1 (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))))))
  have p2c : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (q0 ◇ q1)) (p29 q0 q1)).trans (p29 q0 q1)).symm).trans (((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ q1)) (pg q0 q1))).symm).trans (p2b (q1 ◇ q1) (q0 ◇ q1)))).symm
  have p2d : forall (q0 q1:G), ((q1 ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ q0) (p25 q0 (q1 ◇ q0) (q1 ◇ q0))).trans (cg (fun t => t ◇ q0) (p2c q1 q0))).trans (p1z q1 q0)).symm).trans ((((cg (fun t => t ◇ q0) (cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (p2c q1 q0))))).symm).trans (p18 (q1 ◇ q0) q0 q1)).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ q0) ◇ t) (p2c q1 q0))).trans (p26 q0 (q1 ◇ q0) q0)).trans (cg (fun t => (q1 ◇ q0) ◇ t) (p26 q1 q0 q0))).trans (p25 q0 (q1 ◇ q0) q0)))).symm
  have p2e : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q1) ◇ t) (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))).trans (p2c q0 q1)).symm).trans ((((cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1))))) (p2 q0 q1 q0)).symm).trans (p2c q1 (q0 ◇ (q0 ◇ (q0 ◇ q1))))).trans ((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q1))) ◇ t) (p2 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))))).trans (ps q0 q1)))
  have p2f : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (p28 q1 (q0 ◇ q1) (q0 ◇ q1))).trans (cg (fun t => q1 ◇ t) (p2d q1 q0))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p2d q1 q0))))).symm).trans (p1s q1 (q0 ◇ q1)))).symm
  have p2g : forall (q0 q1:G), (q1 ◇ (q1 ◇ q1)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((p2f q0 q1).symm).trans ((p0 q0 q1).trans (p2e q0 q1))
  have p2h : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((p7 q0 q1).symm).trans ((((cg (fun t => q1 ◇ t) (p2g q0 (q1 ◇ q1))).symm).trans (p7 (q1 ◇ q1) q1)).trans (p2d q1 q1))).symm
  exact ((p2h x y).symm).trans (p2h (y ◇ z) y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41890_to_391 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41890_to_391
