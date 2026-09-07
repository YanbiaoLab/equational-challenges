-- Equation6678 → Equation45046
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x ◇ x = x ◇ (((x ◇ y) ◇ y) ◇ y)
-- Original submission SHA-256: b4e2dc9edbea8f5d9897148fb76ac2fe4349b130350ec5c86ded6523c28576b7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = x ◇ (((x ◇ y) ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), (((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ (q1 ◇ (q1 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ t) ((h (q1 ◇ (q1 ◇ q0)) q1 q0).symm)).symm).trans ((h q1 ((q1 ◇ (q1 ◇ q0)) ◇ q0) (q1 ◇ q0)).symm)
  have p1 : forall (x y z:G), (y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))) = (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p2 : forall (x y z:G), (x ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) = x:=by
    intro x y z
    exact ((h x x x).trans (p1 x x x)).symm
  have p3 : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p2 q0 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p2 q0 q0 q0))).symm).trans (p0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0))
  have p4 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact (((((cg (fun t => t ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0))) (cg (fun t => t ◇ q0) (p3 q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p3 q0)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p3 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0))) (cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p3 q0)))).symm).trans (p0 q0 (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm
  have p5 : forall (x y z q0:G), (x ◇ ((x ◇ x) ◇ x)) = x:=by
    intro x y z q0
    exact ((cg (fun t => x ◇ t) (p4 x)).symm).trans (p2 x x x)
  have p6 : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ q0) (p4 q0)).symm).trans (p3 q0)
  have p7 : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p5 q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)) (q0 ◇ ((q0 ◇ q0) ◇ q0)) (q0 ◇ ((q0 ◇ q0) ◇ q0))))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => q0 ◇ t) (p5 q0 q0 q0 q0)))).symm).trans (p0 ((q0 ◇ q0) ◇ q0) q0))
  have p8 : forall (q0 q1:G), (((q1 ◇ q1) ◇ q1) ◇ (q0 ◇ ((q0 ◇ q1) ◇ q1))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p6 q1)))).symm).trans ((h q0 ((q1 ◇ q1) ◇ q1) q1).symm)
  have p9 : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0))).symm).trans (p8 (q0 ◇ q0) q0)
  have pa : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p9 q0))).symm).trans ((h (q0 ◇ q0) (q0 ◇ q0) q0).symm)
  have pb : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact (((cg (fun t => ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pa q0))).trans (p6 ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans (((cg (fun t => ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pa q0)))).symm).trans (p8 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0))))
  have pc : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q1 ◇ ((q0 ◇ q0) ◇ q0))))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q0) ◇ q0))) (p5 q0 q0 q0 q0)))).symm).trans ((h q0 q1 ((q0 ◇ q0) ◇ q0)).symm)
  have pd : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ (q0 ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))))) ((h q0 q2 q1).symm)))).symm).trans ((h q2 q3 (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))).symm)
  have pe : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) ((h q0 q1 q0).symm)))).symm).trans (pd q0 q0 q1 q1)
  have pf : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (pe q0 q1)).symm).trans (((cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (pe q0 (q1 ◇ (q0 ◇ q0))))).symm).trans ((h q1 (q1 ◇ (q0 ◇ q0)) (q0 ◇ q0)).symm))
  have pg : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q0)) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ q1))) (cg (fun t => t ◇ q1) (pf q0 q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (pf q0 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pf q0 q1))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q0)) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (pf q0 q1)))).symm).trans (p0 q1 (q1 ◇ (q0 ◇ q0))))).symm
  have ph : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = ((q1 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ t) (pf q0 (q1 ◇ q1))).symm).trans (pe q1 ((q1 ◇ q1) ◇ (q0 ◇ q0)))
  have pi : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ (q1 ◇ q1)) (pb q1))).trans (cg (fun t => t ◇ (q1 ◇ q1)) (pb q1))).trans (pb q1)).symm).trans (((cg (fun t => t ◇ (q1 ◇ q1)) (pg q0 (q1 ◇ q1))).symm).trans (ph q0 q1))).symm
  have pj : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (q0 ◇ q0)) (pi q0 q0))).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (pi q0 q1)))).trans (cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (pi q0 q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pi q1 q1))).trans (pi q1 q0)).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (pi q0 q1)))).symm).trans (p8 (q1 ◇ q1) (q0 ◇ q0)))).symm
  have pk : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (pj q0 q1))).symm).trans (p5 q1 q0 q0 q0)
  have pl : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pj q0 q1))).symm).trans (p6 q1)
  have pm : forall (q0 q1:G), ((q1 ◇ q1) ◇ q1) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) (cg (fun t => t ◇ q1) (pl q0 q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pl q0 q1)))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pl q0 q1))).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pl q0 q1)))).symm).trans (p0 q1 ((q0 ◇ q0) ◇ q1)))
  have pn : forall (q1 q2 q0:G), (q2 ◇ (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ (q2 ◇ q1)))) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q2 q0
    exact ((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (pg q0 q1)))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (pk q1 q1)))))).trans (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q1 ◇ (q2 ◇ q1))) (pg q0 q1)))).symm).trans ((((cg (fun t => q2 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (pe q0 (q1 ◇ (q0 ◇ q0)))))))).symm).trans (pd q1 (q0 ◇ q0) (q1 ◇ (q0 ◇ q0)) q2)).trans (pg q0 q1))
  have po : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q1 ◇ q2)) (pj q0 q2)))).symm).trans ((h q2 q1 q2).symm)
  have pp : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q0)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ q2) ◇ t) (pj q0 q2)))).symm).trans ((h q1 q2 q2).symm)
  have pq : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (cg (fun t => t ◇ q1) (pj q0 q1))).symm).trans (p9 q1)
  have pr : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2)) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q2) ◇ t) (cg (fun t => t ◇ q2) (pj q0 q2))).symm).trans (pq q1 q2)
  have ps : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (p9 q0)).symm).trans (pm q1 ((q0 ◇ q0) ◇ q0))).symm
  have pt : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ q1)) = ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (pr q0 q0 q1)).symm).trans (pm q2 ((q0 ◇ q0) ◇ q1))).symm
  have pu : forall (q0 q1:G), ((((q1 ◇ q1) ◇ q1) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (((q1 ◇ q1) ◇ q1) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (pk q1 q1))).symm).trans (((cg (fun t => (((q1 ◇ q1) ◇ q1) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (pf q0 ((q1 ◇ q1) ◇ q1))))).symm).trans (pc q1 (((q1 ◇ q1) ◇ q1) ◇ (q0 ◇ q0))))
  have pv : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (p7 q0)).symm).trans (pe q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))
  have pw : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact (((pt q0 q1 q2).symm).trans (((cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q1) (pj q0 q1))).symm).trans (ps q1 q2))).symm
  have px : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ ((q1 ◇ q2) ◇ q2))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q2) ◇ q2))) (cg (fun t => t ◇ q2) (pj q0 q2))).symm).trans (p8 q1 q2)
  have py : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)) ◇ (q2 ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ q2)) (cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ q2) (pj q0 q2)))).symm).trans (pu q1 q2)
  have pz : forall (q0 q1:G), (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q1) = ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (pj q0 q1))).symm).trans (pv q1)
  have p10 : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) = (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((((((cg (fun t => ((((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (pz q0 q1))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => t ◇ q1) (pr q1 q0 ((q1 ◇ q1) ◇ q1))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))) (cg (fun t => t ◇ q1) (pr q1 q1 q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (pr q1 q0 ((q1 ◇ q1) ◇ q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ q1) ◇ t) (pr q1 q1 q1))).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q1))) (cg (fun t => t ◇ q1) (cg (fun t => ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (pz q0 q1)))).symm).trans (p0 q1 ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1))))).symm
  have p11 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (pg q1 (q0 ◇ q1)))).symm).trans ((h q0 q1 q1).symm)
  have p12 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ q2)) (pj q0 (q1 ◇ q2))))).symm).trans (p11 q1 q2)
  have p13 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q2)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q2)) (pj q0 q2)).symm).trans ((pw q1 q2 q0).symm)).trans (p10 q2 q2)
  have p14 : forall (q0 q1 q2 q3:G), ((((q1 ◇ q1) ◇ q3) ◇ (q2 ◇ q2)) ◇ (q0 ◇ q0)) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (((q1 ◇ q1) ◇ q3) ◇ (q2 ◇ q2)) ◇ t) (pj q0 q3)).symm).trans (py q1 q2 q3)
  have p15 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ (q2 ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (cg (fun t => q2 ◇ t) ((h q2 (q1 ◇ q1) q0).symm))).symm).trans (p12 q1 q2 ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))
  have p16 : forall (q0 q1 q2 q3:G), ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact (((((((cg (fun t => t ◇ (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => q2 ◇ t) (pi q2 q3))).trans (cg (fun t => t ◇ (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))) (pg q3 q2))).trans (pg ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ((q2 ◇ q2) ◇ q2))).trans (cg (fun t => t ◇ ((q2 ◇ q2) ◇ q2)) (pr q2 q2 q2))).trans (p13 q2 q2 q2)).symm).trans (((cg (fun t => t ◇ (((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q2 ◇ q2))) (p15 q0 q1 q2))).symm).trans (p15 (q2 ◇ q2) q3 ((q2 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0))))).symm
  have p17 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ ((q2 ◇ q0) ◇ q2)) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => (q2 ◇ q0) ◇ t) (p15 q0 q1 q2))).symm).trans (pp q2 (q2 ◇ q0) ((q1 ◇ q1) ◇ q0))
  have p18 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ q1)) ◇ q1) = (((q2 ◇ q2) ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q2 ◇ q2) ◇ q1) ◇ t) (p0 q1 q0)).symm).trans (p17 q1 q2 (q0 ◇ (q0 ◇ q1)))).symm
  have p19 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q1) ◇ q0) = (((q0 ◇ q0) ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact ((p18 q0 q1 q2).symm).trans (p18 q0 q1 q0)
  have p1a : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ q0) = ((q0 ◇ (q0 ◇ q1)) ◇ q1):=by
    intro q0 q1
    exact ((p19 q0 q1 q1).symm).trans (((cg (fun t => t ◇ q0) ((pm q0 q1).symm)).symm).trans ((p18 q0 q1 q0).symm))
  have p1b : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q0) ◇ q1) = (((q0 ◇ q0) ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ q1) (pn q0 (q2 ◇ q2) q0)).symm).trans (p19 q1 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q2 ◇ q2) ◇ q0))) q2)).trans ((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pk q2 q0)))).trans (cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ q1) ◇ t) (pl q0 q0))))).symm
  have p1c : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q0)) ◇ q0) = (((q0 ◇ q0) ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q1) (pn q0 (q1 ◇ q1) q0)).symm).trans (p1a q1 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q1) ◇ q0))))).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pk q1 q0))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q1) ◇ q0)))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (pl q0 q0))))).trans (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pk q1 q0)))).trans (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) (pl q0 q0)))).symm
  have p1d : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q1) ◇ q2) = (((q0 ◇ q0) ◇ q1) ◇ q2):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q2) (cg (fun t => t ◇ q1) (pj q0 q2))).symm).trans (p1b q1 q2 q0)).symm
  have p1e : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q1) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((pg (q1 ◇ q0) q1).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ((h q1 q1 q0).symm)).symm).trans (p1c ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1)).trans ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (pi (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => t ◇ q1) (pi (q1 ◇ q0) (q1 ◇ q0)))))).symm
  have p1f : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact (((pr q2 q1 q1).symm).trans ((((cg (fun t => t ◇ ((q2 ◇ q2) ◇ q1)) (p1e q0 q1)).symm).trans (p16 q1 q2 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q0)).trans ((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (pi (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) (pi (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (pi (q1 ◇ q0) (q1 ◇ q0)))).trans (pi (q1 ◇ q0) (q1 ◇ q0))))).symm
  have p1g : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q1 ◇ q0)) = ((q1 ◇ q1) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q1 ◇ q0)) (p1f q0 q1 q0)).symm).trans (pm q2 (q1 ◇ q0))).symm
  have p1h : forall (q0 q2 q3 q1:G), ((q3 ◇ q3) ◇ (q2 ◇ q0)) = ((q0 ◇ q0) ◇ (q2 ◇ q0)):=by
    intro q0 q2 q3 q1
    exact (((cg (fun t => (q3 ◇ q3) ◇ t) (p17 q0 q1 q2)).symm).trans (p1g ((q2 ◇ q0) ◇ q2) ((q1 ◇ q1) ◇ q0) q3)).trans ((cg (fun t => t ◇ (((q1 ◇ q1) ◇ q0) ◇ ((q2 ◇ q0) ◇ q2))) (pr q1 q1 q0)).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p17 q0 q1 q2)))
  have p1i : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)) ◇ q2) = (((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)) ◇ t) (p14 ((((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)) ◇ q0) q0 q1 q2)).symm).trans ((h (((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)) (((q0 ◇ q0) ◇ q2) ◇ (q1 ◇ q1)) q0).symm)
  have p1j : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ q3) ◇ (q2 ◇ q2)) = (((q1 ◇ q1) ◇ q3) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((p1i q1 q0 q3).symm).trans (((cg (fun t => t ◇ q3) (cg (fun t => ((q1 ◇ q1) ◇ q3) ◇ t) (pj q0 q2))).symm).trans (p1i q1 q2 q3))).symm
  have p1k : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ q3) ◇ (q1 ◇ q1)) = (((q1 ◇ q1) ◇ q3) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((p1j q0 q1 q2 q3).symm).trans (p1j q1 q1 q2 q3)).symm
  have p1l : forall (q0 q2 q3 q1:G), ((q2 ◇ q0) ◇ ((q2 ◇ q2) ◇ ((q2 ◇ q0) ◇ q2))) = q0:=by
    intro q0 q2 q3 q1
    exact ((cg (fun t => (q2 ◇ q0) ◇ t) (p1h q2 (q2 ◇ q0) q3 ((q3 ◇ q3) ◇ ((q2 ◇ q0) ◇ q2)))).symm).trans ((((cg (fun t => t ◇ ((q3 ◇ q3) ◇ ((q2 ◇ q0) ◇ q2))) (p17 q0 q1 q2)).symm).trans (p16 ((q2 ◇ q0) ◇ q2) q3 ((q1 ◇ q1) ◇ q0) q0)).trans ((((cg (fun t => t ◇ (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0))) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q0)) (pr q1 q1 q0))).trans (cg (fun t => t ◇ (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0))) (p13 q0 q1 q0))).trans (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pr q1 q1 q0))).trans (p14 q0 q0 q0 q0)))
  have p1m : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ q2) ◇ (q1 ◇ q2))) = (q1 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q1))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q2) (po q0 q2 q1)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q2 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q1)))) ◇ q2))) (po q0 q2 q1)).symm).trans (p1l (q1 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q1))) q2 q0 q0))
  have p1n : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ q2) ◇ (q1 ◇ q2))) = (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q2) (p12 q0 q1 q2)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q2 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))) ◇ q2))) (p12 q0 q1 q2)).symm).trans (p1l (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2))) q2 q0 q0))
  have p1o : forall (q1 q2 q3 q0:G), (q3 ◇ ((q2 ◇ q2) ◇ q1)) = (q3 ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q1 q2 q3 q0
    exact (((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q1) (p1f ((q0 ◇ q0) ◇ (q3 ◇ q1)) q1 ((q1 ◇ ((q0 ◇ q0) ◇ (q3 ◇ q1))) ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q3 ◇ q1))))))).symm).trans ((((cg (fun t => q3 ◇ t) (cg (fun t => ((q1 ◇ ((q0 ◇ q0) ◇ (q3 ◇ q1))) ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q3 ◇ q1)))) ◇ t) (po q0 q3 q1))).symm).trans (p1n q2 q3 (q1 ◇ ((q0 ◇ q0) ◇ (q3 ◇ q1))))).trans (cg (fun t => q3 ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (po q0 q3 q1))))).symm
  have p1p : forall (q0 q1 q2 q3:G), (q2 ◇ ((q1 ◇ q1) ◇ (q3 ◇ q2))) = (q2 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q3))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ q3)) (pj q0 q3))).symm).trans (p1m q1 q2 q3)).symm
  have p1q : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ (q1 ◇ q1)) = (((q0 ◇ q0) ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q1))) (pr q0 q0 q1))).trans (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (pr q0 q0 q1)))).trans (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (p1f q1 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1))))).symm).trans ((p1m ((q0 ◇ q0) ◇ q1) ((q0 ◇ q0) ◇ q1) ((q0 ◇ q0) ◇ q1)).trans ((p1k (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)) q0 q0 q1).symm))
  have p1r : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((p1m q0 q1 q0).trans (p1o (q0 ◇ q1) q0 q1 q0)).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (p1f q1 q0 ((q0 ◇ q1) ◇ (q0 ◇ q1)))))
  have p1s : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q0)) = ((q0 ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((((cg (fun t => (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p1r q0 q1)))).trans (p1l ((q0 ◇ q0) ◇ (q0 ◇ q1)) q1 ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1))) ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1))))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ q1))) (p1r q0 q1)).symm).trans (p1l ((q0 ◇ q0) ◇ (q1 ◇ q0)) q1 q0 q0))).symm
  have p1t : forall (q0 q2 q1 q3:G), (q2 ◇ q0) = (q0 ◇ q2):=by
    intro q0 q2 q1 q3
    exact ((p14 q1 q2 q3 (q2 ◇ q0)).symm).trans (((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ (q3 ◇ q3)) (p1s q2 q0))).symm).trans (p14 q1 q2 q3 (q0 ◇ q2)))
  have p1u : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q1 ◇ q0)) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))).symm).trans (p1f q0 q1 q2)
  have p1v : forall (q0 q1 q2 q3:G), (((q0 ◇ q1) ◇ q1) ◇ q0) = (((q0 ◇ q0) ◇ q0) ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ q0) (cg (fun t => q1 ◇ t) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))).trans (cg (fun t => t ◇ q0) (p1t (q0 ◇ q1) q1 (q1 ◇ (q0 ◇ q1)) (q1 ◇ (q0 ◇ q1))))).symm).trans (p1c q0 q1)
  have p1w : forall (q0 q1 q2:G), (((q1 ◇ q2) ◇ (q2 ◇ q2)) ◇ q1) = (((q0 ◇ q0) ◇ (q1 ◇ q2)) ◇ q1):=by
    intro q0 q1 q2
    exact (((((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q2 ◇ q1)) (cg (fun t => t ◇ (q2 ◇ q1)) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q2 ◇ q1)) (cg (fun t => (q1 ◇ q2) ◇ t) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1)))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => ((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ t) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q1 ◇ q2)) (p1u q1 q2 ((q1 ◇ q2) ◇ (q1 ◇ q2)) ((q1 ◇ q2) ◇ (q1 ◇ q2)))))).trans (cg (fun t => q1 ◇ t) (p1t (q1 ◇ q2) (q2 ◇ q2) ((q2 ◇ q2) ◇ (q1 ◇ q2)) ((q2 ◇ q2) ◇ (q1 ◇ q2))))).trans (p1t ((q1 ◇ q2) ◇ (q2 ◇ q2)) q1 (q1 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q2))) (q1 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q2))))).symm).trans ((((cg (fun t => q1 ◇ t) ((pm q0 (q2 ◇ q1)).symm)).symm).trans (p1p q0 q0 q1 q2)).trans (p1t ((q0 ◇ q0) ◇ (q1 ◇ q2)) q1 (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2))) (q1 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q2)))))
  have p1x : forall (q1 q2 q3 q0:G), (((((q1 ◇ q1) ◇ q1) ◇ q2) ◇ (q3 ◇ q3)) ◇ q1) = q2:=by
    intro q1 q2 q3 q0
    exact (((((cg (fun t => q1 ◇ t) (cg (fun t => (q3 ◇ q3) ◇ t) (p1t ((q1 ◇ q2) ◇ q2) q1 (q1 ◇ ((q1 ◇ q2) ◇ q2)) (q1 ◇ ((q1 ◇ q2) ◇ q2))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => (q3 ◇ q3) ◇ t) (p1v q1 q2 (((q1 ◇ q2) ◇ q2) ◇ q1) (((q1 ◇ q2) ◇ q2) ◇ q1))))).trans (cg (fun t => q1 ◇ t) (p1t (((q1 ◇ q1) ◇ q1) ◇ q2) (q3 ◇ q3) ((q3 ◇ q3) ◇ (((q1 ◇ q1) ◇ q1) ◇ q2)) ((q3 ◇ q3) ◇ (((q1 ◇ q1) ◇ q1) ◇ q2))))).trans (p1t ((((q1 ◇ q1) ◇ q1) ◇ q2) ◇ (q3 ◇ q3)) q1 (q1 ◇ ((((q1 ◇ q1) ◇ q1) ◇ q2) ◇ (q3 ◇ q3))) (q1 ◇ ((((q1 ◇ q1) ◇ q1) ◇ q2) ◇ (q3 ◇ q3))))).symm).trans ((((cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q1 ◇ ((q1 ◇ q2) ◇ q2)))) (px q0 q1 q2)).symm).trans (p16 (q1 ◇ ((q1 ◇ q2) ◇ q2)) q3 ((q0 ◇ q0) ◇ q2) q0)).trans (((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q2)) (p1u (q0 ◇ q0) q2 (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2)) (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2))) (p1t ((q0 ◇ q0) ◇ q2) (q2 ◇ q2) ((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ q2)) ((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ q2))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2))) (p1q q0 q2))).trans (cg (fun t => (((q0 ◇ q0) ◇ q2) ◇ (q0 ◇ q0)) ◇ t) (p1u (q0 ◇ q0) q2 (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2)) (((q0 ◇ q0) ◇ q2) ◇ ((q0 ◇ q0) ◇ q2))))).trans (p14 q2 q0 q0 q2)))
  have p1y : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q0) ◇ q2) ◇ (((q0 ◇ q1) ◇ (q1 ◇ q2)) ◇ q0)) = q2:=by
    intro q0 q1 q2
    exact (((((cg (fun t => t ◇ (q2 ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1))))).trans (cg (fun t => (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q2))) ◇ t) (p1t ((q0 ◇ q0) ◇ q0) q2 (q2 ◇ ((q0 ◇ q0) ◇ q0)) (q2 ◇ ((q0 ◇ q0) ◇ q0))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)) (p1t ((q0 ◇ q1) ◇ (q1 ◇ q2)) q0 (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q2))) (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q2)))))).trans (p1t (((q0 ◇ q0) ◇ q0) ◇ q2) (((q0 ◇ q1) ◇ (q1 ◇ q2)) ◇ q0) ((((q0 ◇ q1) ◇ (q1 ◇ q2)) ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)) ((((q0 ◇ q1) ◇ (q1 ◇ q2)) ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)))).symm).trans (((cg (fun t => (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))) ◇ t) (cg (fun t => q2 ◇ t) (pg (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1))) q0))).symm).trans (pd q0 q1 q2 (q0 ◇ ((q0 ◇ q1) ◇ (q2 ◇ q1)))))
  have p1z : forall (q0 q1 q2:G), (((q0 ◇ q2) ◇ (q1 ◇ q1)) ◇ q2) = (((q0 ◇ q0) ◇ (q0 ◇ q2)) ◇ q2):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ q2) (cg (fun t => t ◇ (q0 ◇ q0)) (p1t q0 q2 (q2 ◇ q0) (q2 ◇ q0)))).trans (cg (fun t => t ◇ q2) (p1t (q0 ◇ q0) (q0 ◇ q2) ((q0 ◇ q2) ◇ (q0 ◇ q0)) ((q0 ◇ q2) ◇ (q0 ◇ q0))))).symm).trans (((p1w (q2 ◇ q0) q2 q0).trans (p1d q1 (q2 ◇ q0) q2)).trans ((cg (fun t => t ◇ q2) (cg (fun t => (q1 ◇ q1) ◇ t) (p1t q0 q2 (q2 ◇ q0) (q2 ◇ q0)))).trans (cg (fun t => t ◇ q2) (p1t (q0 ◇ q2) (q1 ◇ q1) ((q1 ◇ q1) ◇ (q0 ◇ q2)) ((q1 ◇ q1) ◇ (q0 ◇ q2))))))).symm
  have p20 : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact (((cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (cg (fun t => q2 ◇ t) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1)))).trans (cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (p1t (q1 ◇ q2) q2 (q2 ◇ (q1 ◇ q2)) (q2 ◇ (q1 ◇ q2))))).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q2 ◇ q1))) (p18 q2 q1 q0)).symm).trans (p0 q1 q2))
  have p21 : forall (q0 q1 q2:G), ((((q1 ◇ q2) ◇ q2) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact (((((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q2) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q1 ◇ q2) ◇ q2))) (p1t q1 q2 (q2 ◇ q1) (q2 ◇ q1)))).trans (cg (fun t => (q1 ◇ q2) ◇ t) (p1t ((q1 ◇ q2) ◇ q2) (q0 ◇ q0) ((q0 ◇ q0) ◇ ((q1 ◇ q2) ◇ q2)) ((q0 ◇ q0) ◇ ((q1 ◇ q2) ◇ q2))))).trans (p1t (((q1 ◇ q2) ◇ q2) ◇ (q0 ◇ q0)) (q1 ◇ q2) ((q1 ◇ q2) ◇ (((q1 ◇ q2) ◇ q2) ◇ (q0 ◇ q0))) ((q1 ◇ q2) ◇ (((q1 ◇ q2) ◇ q2) ◇ (q0 ◇ q0))))).symm).trans (((cg (fun t => (q2 ◇ q1) ◇ t) (cg (fun t => t ◇ ((q2 ◇ q1) ◇ q2)) (pj q0 q2))).symm).trans (p1l q1 q2 q0 q0))
  have p22 : forall (q0 q1:G), ((((q0 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ q0) = q1:=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q0 ◇ q1)) (p1u q0 q1 ((q0 ◇ q1) ◇ (q0 ◇ q1)) ((q0 ◇ q1) ◇ (q0 ◇ q1)))))).trans (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q1) (p1t (q0 ◇ q1) (q1 ◇ q1) ((q1 ◇ q1) ◇ (q0 ◇ q1)) ((q1 ◇ q1) ◇ (q0 ◇ q1)))))).trans (cg (fun t => t ◇ q0) (p1z q0 q1 q1))).symm).trans (((cg (fun t => ((((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ q1) ◇ t) (p21 q1 q0 q1)).symm).trans (p1y (q0 ◇ q1) q1 q1))
  have p23 : forall (q0 q1 q2 q3:G), (((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ (q3 ◇ q3)) ◇ q1) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q3 ◇ q3)) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q1) (pj q0 q1))))).symm).trans (p1x q1 q2 q3 q0)
  have p24 : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q0) ◇ (q1 ◇ q1)) ◇ q0) = (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((((((((((((cg (fun t => q0 ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1))) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0))))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => (q0 ◇ q1) ◇ t) (p1t ((q0 ◇ q1) ◇ q1) (q1 ◇ q1) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)))))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1))) ◇ (q1 ◇ q0))) (cg (fun t => t ◇ (q1 ◇ q0)) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1))) ◇ (q1 ◇ q0))) (cg (fun t => (q0 ◇ q1) ◇ t) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1))) ◇ t) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (p1t (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) (q0 ◇ q1) ((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1))) ((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)))))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (p21 q1 q0 q1))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (p1t (q0 ◇ q1) q0 (q0 ◇ (q0 ◇ q1)) (q0 ◇ (q0 ◇ q1)))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q0)) (p1u q0 q1 ((q0 ◇ q1) ◇ (q0 ◇ q1)) ((q0 ◇ q1) ◇ (q0 ◇ q1)))))).trans (cg (fun t => q0 ◇ t) (p1t ((q0 ◇ q1) ◇ q0) (q1 ◇ q1) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q0)) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q0))))).trans (p1t (((q0 ◇ q1) ◇ q0) ◇ (q1 ◇ q1)) q0 (q0 ◇ (((q0 ◇ q1) ◇ q0) ◇ (q1 ◇ q1))) (q0 ◇ (((q0 ◇ q1) ◇ q0) ◇ (q1 ◇ q1))))).symm).trans ((((cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (((q1 ◇ q0) ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q0) ◇ q1))) ◇ (q1 ◇ q0)))) (p1l q0 q1 q0 q0)).symm).trans (p1l ((q1 ◇ q1) ◇ ((q1 ◇ q0) ◇ q1)) (q1 ◇ q0) q0 q0)).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))).trans (p1t ((q0 ◇ q1) ◇ q1) (q1 ◇ q1) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)) ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)))))
  have p25 : forall (q0 q1 q2:G), ((((q1 ◇ q2) ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact (((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) (cg (fun t => t ◇ (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2))) (p1t (((q0 ◇ q0) ◇ q1) ◇ q2) q2 (q2 ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) (q2 ◇ (((q0 ◇ q0) ◇ q1) ◇ q2))))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) (cg (fun t => ((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ q2) ◇ t) (p1u (q1 ◇ q2) q2 (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2)) (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2)))))).trans (p21 q2 ((q0 ◇ q0) ◇ q1) q2)).symm).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) (cg (fun t => t ◇ (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2))) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q2)) (p20 q0 q1 q2)))).symm).trans (p24 (((q0 ◇ q0) ◇ q1) ◇ q2) ((q1 ◇ q2) ◇ q2))).trans (((cg (fun t => t ◇ (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2))) (cg (fun t => t ◇ ((q1 ◇ q2) ◇ q2)) (p20 q0 q1 q2))).trans (cg (fun t => t ◇ (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2))) (p1t ((q1 ◇ q2) ◇ q2) q2 (q2 ◇ ((q1 ◇ q2) ◇ q2)) (q2 ◇ ((q1 ◇ q2) ◇ q2))))).trans (cg (fun t => (((q1 ◇ q2) ◇ q2) ◇ q2) ◇ t) (p1u (q1 ◇ q2) q2 (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2)) (((q1 ◇ q2) ◇ q2) ◇ ((q1 ◇ q2) ◇ q2))))))).symm
  have p26 : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q1) ◇ ((q1 ◇ q2) ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q2) ◇ q2)) (p25 q0 q1 q2)).symm).trans (p21 q2 (q1 ◇ q2) q2)
  have p27 : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q2 ◇ q2)) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))).trans (p1z q0 q2 q1)).symm).trans ((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q2 ◇ q2)) (p26 q0 q1 q0))).symm).trans (p23 q0 q1 ((q1 ◇ q0) ◇ q0) q2)).trans (cg (fun t => t ◇ q0) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0))))
  have p28 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q0) ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q0) (p27 q0 q1 (((q0 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1))).symm).trans (p22 q0 q1)
  have p29 : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q1) = q0:=by
    intro q0 q1
    exact ((((p28 q1 q0 q0).symm).trans (p1t q1 ((q1 ◇ q0) ◇ q1) q0 q0)).trans ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (p1t q0 q1 (q1 ◇ q0) (q1 ◇ q0)))).trans (p1t ((q0 ◇ q1) ◇ q1) q1 (q1 ◇ ((q0 ◇ q1) ◇ q1)) (q1 ◇ ((q0 ◇ q1) ◇ q1))))).symm
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = (x ◇ (((x ◇ y) ◇ y) ◇ y)):=(cg (fun t => x ◇ t) (p29 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6678_to_45046 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6678_to_45046
