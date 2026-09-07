-- Equation19010 → Equation19756
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
-- Conclusion: x = (x ◇ y) ◇ ((z ◇ (y ◇ z)) ◇ y)
-- Original submission SHA-256: f7ea06b5f22046e9d6fb055eebbdec8857bb92ee63066177b81c68132982feee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((z ◇ (y ◇ z)) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))) = ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (x y z:G), ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) = x:=by
    intro x y z
    exact ((h x x x).trans (p0 x x x)).symm
  have p2 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q3) ◇ ((((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ q0)) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))).symm)
  have p3 : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) q3 (q1 ◇ q0)).symm)
  have p4 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) ((h q0 q1 q2).symm)).symm).trans (p3 q0 q1 q2 (q1 ◇ q0))
  have p5 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p4 q0 q1 q2).symm).trans (p4 q0 q1 q0)
  have p6 : forall (x y z q0 q1 q2:G), ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ x))) = x:=by
    intro x y z q0 q1 q2
    exact ((h x y x).trans (cg (fun t => (y ◇ x) ◇ t) (p5 x y x))).symm
  have p7 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (p4 q0 q1 q2).trans (p5 q0 q1 q2)
  have p8 : forall (q0 q1 q3 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0) = ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q3)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q3) (p5 q0 q1 q2))).symm).trans (((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p5 q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))))
  have p9 : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ q3) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = ((q3 ◇ q3) ◇ ((q2 ◇ q0) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q2) ◇ q3) ◇ t) (p5 q0 q1 q2)).symm).trans (p5 q3 (q2 ◇ q0) (q1 ◇ q2))
  have pa : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ (q3 ◇ (q1 ◇ q2))) = (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q3 ◇ (q2 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q3 ◇ (q2 ◇ q0))) (p5 q0 q1 q2)).symm).trans (p5 (q1 ◇ q2) q3 (q2 ◇ q0))).symm
  have pb : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ (q3 ◇ (q2 ◇ q1))) = (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q3 ◇ (q2 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((pa q0 q1 q2 q3).symm).trans (pa q1 q1 q2 q3)).symm
  have pc : forall (q0 q1 q2:G), ((((q1 ◇ q0) ◇ q0) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2))) ◇ q0) = ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q1 ◇ q0) ◇ q0) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2))) ◇ t) ((h q0 q1 (q1 ◇ q0)).symm)).symm).trans (p3 (q1 ◇ q0) q1 q2 ((q1 ◇ q0) ◇ q0))
  have pd : forall (q0 q1:G), (((q1 ◇ q1) ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) ◇ q1) = ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (p5 q1 (q1 ◇ (q0 ◇ q1)) (q0 ◇ q1))).symm).trans (pc q1 q0 q1)
  have pe : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q2)) = ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ q0) (p9 (q1 ◇ q0) q1 q0 q0)).trans (pd q1 q0)).symm).trans (((cg (fun t => t ◇ q0) (cg (fun t => ((q1 ◇ q0) ◇ q0) ◇ t) (p5 (q1 ◇ q0) q1 q2))).symm).trans (pc q0 q1 q2))).symm
  have pf : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q1 ◇ q0))) = ((q1 ◇ (q2 ◇ q1)) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (p5 q0 q2 q1)).symm).trans (pe q1 q2 (q1 ◇ q0))
  have pg : forall (q0 q1:G), ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p1 q0 q0 q0))).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 (q0 ◇ q0)).symm)
  have ph : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (((q1 ◇ (q0 ◇ q0)) ◇ q0) ◇ q2)) = ((q2 ◇ q2) ◇ ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q2)):=by
    intro q0 q1 q2
    exact ((p9 q0 q0 (q1 ◇ (q0 ◇ q0)) q2).symm).trans (((cg (fun t => ((q0 ◇ (q1 ◇ (q0 ◇ q0))) ◇ q2) ◇ t) (pg q0 q1)).symm).trans (p5 q2 (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (q0 ◇ (q1 ◇ (q0 ◇ q0)))))
  have pi : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (p8 q0 q0 q0 q0)).symm).trans (ph q0 (q0 ◇ q0) q0)).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))
  have pj : forall (q0 q1 q2 q3:G), (((q1 ◇ q2) ◇ q3) ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0))) = ((q3 ◇ q3) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q1 ◇ q2) ◇ q3) ◇ t) (pe q0 q1 q2)).symm).trans (p5 q3 (q2 ◇ (q1 ◇ q0)) (q1 ◇ q2))
  have pk : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) (cg (fun t => q3 ◇ t) (p5 q0 q1 q2))).symm).trans ((p3 q0 q1 q2 q3).trans (p5 q0 q1 q2))
  have pl : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ ((((q3 ◇ q3) ◇ (q0 ◇ q3)) ◇ q1) ◇ q2)) = ((q3 ◇ q2) ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q3) ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q3 ◇ q2) ◇ t) (p8 q3 q0 q1 q0)).symm).trans (p5 q2 (((q3 ◇ q3) ◇ (q0 ◇ q3)) ◇ q1) q3)).symm
  have pm : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) = ((q1 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((pl q0 q0 q1 q0).symm).trans (ph q0 (q0 ◇ q0) q1)).trans (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))
  have pn : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))):=by
    intro q0
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pi q0)).symm).trans (pe ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) (q0 ◇ q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (p6 q0 (q0 ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))
  have po : forall (q0:G), ((q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (pn q0)).symm).trans (pe (q0 ◇ q0) (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))
  have pp : forall (q0 q1 q2 q3:G), (q1 ◇ ((((q1 ◇ q1) ◇ (q2 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) ◇ q1)) = ((q0 ◇ q1) ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) (p5 q1 q2 q3)))).symm).trans (((cg (fun t => t ◇ ((((q3 ◇ q1) ◇ (q2 ◇ q3)) ◇ ((q0 ◇ q1) ◇ (q2 ◇ q0))) ◇ q1)) ((h q1 q2 q0).symm)).symm).trans (p2 q1 q2 q3 ((q0 ◇ q1) ◇ (q2 ◇ q0))))
  have pq : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ ((q3 ◇ (q1 ◇ q2)) ◇ ((q2 ◇ q0) ◇ q3))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q3 ◇ (q1 ◇ q2)) ◇ ((q2 ◇ q0) ◇ q3))) (p5 q0 q1 q2)).symm).trans ((h (q1 ◇ q2) (q2 ◇ q0) q3).symm)
  have pr : forall (q0 q1 q2 q3:G), ((q3 ◇ (q1 ◇ q2)) ◇ (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q3 ◇ (q2 ◇ q0)))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ (q1 ◇ q2)) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ q0))) (p5 q0 q1 q2))).symm).trans ((h (q1 ◇ q2) q3 (q2 ◇ q0)).symm)
  have ps : forall (q0 q1 q2:G), (((q1 ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q0 ◇ q1))) ◇ (q2 ◇ q0)) = (q2 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q0 ◇ q1))) ◇ t) (pq q1 q2 q0 q1)).symm).trans (pr q1 q2 (q0 ◇ q1) (q1 ◇ (q2 ◇ q0)))
  have pt : forall (q0 q1 q2:G), (((q0 ◇ (q2 ◇ q0)) ◇ (q2 ◇ q0)) ◇ (q2 ◇ (q1 ◇ (q2 ◇ q0)))) = ((q1 ◇ (q2 ◇ q1)) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q1 ◇ (q2 ◇ q0)))) (pe q0 q2 q1)).symm).trans (pe q1 q2 (q1 ◇ (q2 ◇ q0)))
  have pu : forall (q0 q1:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) (p6 q0 q1 ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))))).symm).trans ((((cg (fun t => (((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0 q1 q0 q0 q0 q0))).symm).trans (pt (q1 ◇ q0) (q1 ◇ q0) (q0 ◇ q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) (p6 q0 q1 ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))))))
  have pv : forall (q0 q2 q1:G), ((q2 ◇ q2) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q2) ◇ q2)) = q2:=by
    intro q0 q2 q1
    exact ((p5 q2 (((q0 ◇ q0) ◇ q0) ◇ q2) (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0)))).symm).trans (((cg (fun t => ((q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ q2) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q2) ◇ t) (pu q0 q1))).symm).trans ((h q2 (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ((q0 ◇ q0) ◇ q0)).symm))
  have pw : forall (q1 q0:G), (q1 ◇ ((q1 ◇ q1) ◇ q1)) = q1:=by
    intro q1 q0
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pv q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)))))).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)) ◇ t) (pv q0 q1 q0)))).symm).trans (pp q1 q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q0)).trans (pv q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))
  have px : forall (q1 q0:G), (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) = q1:=by
    intro q1 q0
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => (q1 ◇ q1) ◇ t) (pv q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))) ◇ t) (cg (fun t => q1 ◇ t) (pv q0 q1 q0))).symm).trans (pk q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q0 (q1 ◇ q1))).trans (pv q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))
  have py : forall (q1 q0:G), ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q1 q0
    exact (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (cg (fun t => q1 ◇ t) (pv q0 q1 q0))).symm).trans (pu q1 (((q0 ◇ q0) ◇ q0) ◇ q1))).trans (cg (fun t => q1 ◇ t) (pv q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1))))
  have pz : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = ((q0 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q1) ◇ t) (py q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))).symm).trans (pm q0 q1)).symm
  have p10 : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact (((cg (fun t => t ◇ q0) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (pw q0 q0)))).symm).trans (pd (q0 ◇ q0) q0)).trans ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (pw q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)))).trans (pw q0 (q0 ◇ ((q0 ◇ q0) ◇ q0))))
  have p11 : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0
    exact (((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p10 q0)))).symm).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0)) (p10 q0)))).symm).trans (p7 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0)).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p10 q0)))).symm
  have p12 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact (((cg (fun t => q0 ◇ t) (pw q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)))).symm).trans (((cg (fun t => t ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) (px q0 q0)).symm).trans (pe q0 q0 ((q0 ◇ q0) ◇ q0)))).symm
  have p13 : forall (q0:G), (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (p11 q0)).symm).trans (pw q0 q0)
  have p14 : forall (q0 q1:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ t) (pv q0 q1 q0)).symm).trans ((h q1 (((q0 ◇ q0) ◇ q0) ◇ q1) q1).symm)
  have p15 : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((pu q0 q0).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pw q0 q0))).symm).trans (ps q0 q0 (q0 ◇ q0)))
  have p16 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ q0) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (py q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))))).symm).trans (po q0)).trans (p15 q0)
  have p17 : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q1)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (cg (fun t => q1 ◇ t) (py q0 q0))).symm).trans (pe ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) q1)).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (py q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (px q0 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))).trans (cg (fun t => q0 ◇ t) (py q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))
  have p18 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact (((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pe q0 q0 (q0 ◇ q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p12 q0))).trans (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p17 q0 (q0 ◇ q0)))).symm).trans (p16 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0)).trans ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (p17 q0 (q0 ◇ q0))).trans (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (p17 q0 (q0 ◇ q0)))))).symm
  have p19 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1)) = (((q0 ◇ q0) ◇ q1) ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (px q0 q0)).symm).trans (p5 q1 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0))).symm
  have p1a : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q1) ◇ q2) ◇ (q0 ◇ q0)) = ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q2) ◇ t) (py q0 q0)).symm).trans (p9 q0 (q0 ◇ q0) q1 q2)
  have p1b : forall (q0 q1:G), (q0 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (p10 q0)).symm).trans (p5 q0 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)))
  have p1c : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ q2)) = (((q0 ◇ q1) ◇ q2) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => ((q0 ◇ q1) ◇ q2) ◇ t) (p12 q0)).symm).trans (pj q0 q0 q1 q2)).symm
  have p1d : forall (q0 q1 q2:G), ((((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q2) ◇ q0) = ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q2) ◇ t) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (((cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q2) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p16 q0 q0))).symm).trans (p9 q0 (q0 ◇ (q0 ◇ q0)) q1 q2))
  have p1e : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ (q0 ◇ q0)) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q1) (p18 q0))).symm).trans (p1d q0 (q0 ◇ (q0 ◇ q0)) q1)).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p16 q0 ((q0 ◇ (q0 ◇ q0)) ◇ q0)))).trans (p1c q0 (q0 ◇ q0) q1))).symm
  have p1f : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ (q1 ◇ q1)))) = ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (p11 q1)).symm).trans (p5 q0 (q1 ◇ q1) q1)
  have p1g : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm).trans ((((cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p5 q0 q0 q0)))).symm).trans (p1f q1 (q0 ◇ q0))).trans ((p1c q0 (q0 ◇ q0) q1).trans (p1e q0 q1)))
  have p1h : forall (q0 q1:G), ((q1 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ q1)) = (q0 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (p18 q0)).symm).trans (pz q1 (q0 ◇ (q0 ◇ q0)))).symm
  have p1i : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ (q0 ◇ q0))) = (q0 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (p18 q0)))).symm).trans ((((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (p18 q0)))).symm).trans (p1b (q0 ◇ (q0 ◇ q0)) q1)).trans (cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (p18 q0)))
  have p1j : forall (q0 q1 q2:G), (q2 ◇ ((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q1))) = ((q2 ◇ q2) ◇ (((q2 ◇ q0) ◇ q1) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (p9 q2 q2 q0 q1)).symm).trans (p1b q2 ((q2 ◇ q0) ◇ q1))
  have p1k : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)) = ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q0)):=by
    intro q0 q1
    exact (((((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p5 q0 q0 q1)))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (p1c q0 (q0 ◇ q0) q1))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (p1e q0 q1))).symm).trans ((((cg (fun t => (q0 ◇ q1) ◇ t) (p1j q0 (q0 ◇ q1) q1)).symm).trans (p1b (q0 ◇ q1) q1)).trans (pz q1 (q0 ◇ q1)))).symm
  have p1l : forall (q0 q1:G), ((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (((((((cg (fun t => t ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p1i q0 q0)))).trans (cg (fun t => t ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p13 q0))))).trans (cg (fun t => t ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (cg (fun t => t ◇ (q1 ◇ q0)) (p1i q0 q0)))).trans (cg (fun t => t ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (cg (fun t => t ◇ (q1 ◇ q0)) (p13 q0)))).trans (cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p1i q0 q0)))).trans (cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p13 q0)))).symm).trans ((((cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) ◇ t) (p1h q0 (q0 ◇ (q0 ◇ q0)))).symm).trans (p1k q1 ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))).trans (((((cg (fun t => (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => q1 ◇ t) (p1i q0 q0)))).trans (cg (fun t => (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => q1 ◇ t) (p13 q0))))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (cg (fun t => q1 ◇ t) (p1i q0 q0)))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (cg (fun t => q1 ◇ t) (p13 q0)))).trans (p5 q0 (q1 ◇ q0) q1)))
  have p1m : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = (((q0 ◇ q0) ◇ q1) ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q1) ◇ t) (pv q0 ((q0 ◇ q0) ◇ q0) q0)).symm).trans (pm ((q0 ◇ q0) ◇ q0) q1)).trans (p19 q0 q1)
  have p1n : forall (q0 q1:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (py q1 ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (pv q0 q1 q0)).symm).trans (pf q1 (((q0 ◇ q0) ◇ q0) ◇ q1) (q1 ◇ q1))).trans ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1))) (cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q1) ◇ t) (p19 q0 q1))).trans (cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) ◇ t) (p19 q0 q1))))).symm
  have p1o : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q1) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (px q0 q0))).symm).trans ((h q1 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0)).symm)
  have p1p : forall (q0 q1:G), (q1 ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q1) ◇ q0)) (p1o q0 q1)).symm).trans (p1n q0 q1)
  have p1q : forall (q0 q1:G), (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((((((((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1g q1 q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1g q1 q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1p q0 ((q1 ◇ q1) ◇ q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1g q1 q1)))).trans (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1g q1 q1))).trans (p1p q0 ((q1 ◇ q1) ◇ q1))).trans (cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1g q1 q1))).trans (p1g q1 q1)).symm).trans (((cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)) (p1p q0 ((q1 ◇ q1) ◇ q1)))).symm).trans (p14 q1 (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q1)) ◇ q0)))).symm
  have p1r : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q1)) = q1:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) (p1q q1 q0)).symm).trans (p1a q1 ((q0 ◇ q0) ◇ q0) q1)).trans (pv q0 q1 ((q1 ◇ q1) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1)))
  have p1s : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = q1:=by
    intro q0 q1
    exact (((p10 q1).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (p1r q0 q1)).symm).trans (pz ((q0 ◇ q0) ◇ q0) (q1 ◇ q1))).trans ((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (p1r q0 q1)).trans (cg (fun t => q1 ◇ t) (p1g q0 q0))))).symm
  have p1t : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact (((p1s q0 ((q0 ◇ q0) ◇ q1)).symm).trans (p1g q0 q1)).symm
  have p1u : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q1)) = q0:=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q1)) (p1s q0 q1)).symm).trans (pe q0 (q0 ◇ q0) q1)).trans ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (p1s q0 q0)).trans (p1s q0 q0))
  have p1v : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (p13 q0))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (p1i q0 q0))).symm).trans (p1u (q0 ◇ (q0 ◇ q0)) q1))
  have p1w : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ q1) = q0:=by
    intro q0 q1
    exact (((p10 q0).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p1r q1 q0)).symm).trans (p19 q1 (q0 ◇ q0)))).symm
  have p1x : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q0 ◇ q0))) = ((q1 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (p1w q0 q1)))).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ q1)) (p1w q0 q1)))).symm).trans (p7 q1 ((q1 ◇ q1) ◇ (q0 ◇ q0)) q0)).trans (cg (fun t => (q1 ◇ q1) ◇ t) (p1w q0 q1)))
  have p1y : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (((p5 q0 q1 q1).symm).trans ((((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => q1 ◇ t) (p1w q0 q1))).symm).trans (p1l q1 ((q1 ◇ q1) ◇ (q0 ◇ q0)))).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p1w q0 q1))).trans (pz q0 q1)))).symm
  have p1z : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (pz q0 q1).trans (p1y q0 q1)
  have p20 : forall (q0 q1:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) = (q1 ◇ q0):=by
    intro q0 q1
    exact (((p1s q1 (q1 ◇ q0)).symm).trans (p5 q0 (q1 ◇ q1) q1)).symm
  have p21 : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q0 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact ((((p20 (q1 ◇ q1) q0).symm).trans ((pb q1 q1 q1 (q0 ◇ q0)).symm)).trans ((p1z (q0 ◇ q0) (q1 ◇ q1)).trans (p20 (q0 ◇ q0) q1))).symm
  have p22 : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q1) = q0:=by
    intro q0 q1
    exact (((p1u q0 (q1 ◇ q0)).symm).trans (((cg (fun t => (q1 ◇ q0) ◇ t) (p5 q0 q1 q1)).symm).trans (p1x q1 (q1 ◇ q0)))).symm
  have p23 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ q0) = ((q2 ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q2 ◇ q1) ◇ t) (p22 q0 q2)).symm).trans (p5 q1 ((q2 ◇ q0) ◇ (q2 ◇ q0)) q2)).trans (p20 q1 (q2 ◇ q0))
  have p24 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = ((q0 ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((p23 q1 (q1 ◇ q1) q0).symm).trans (((cg (fun t => t ◇ q1) (p21 q0 q1)).symm).trans (p1t q1 (q0 ◇ q0)))).symm
  have p25 : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1) = q0:=by
    intro q0 q1
    exact (((p1s q1 q0).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (p1r q1 q0)).symm).trans (p1m q1 (q0 ◇ q0))).trans (cg (fun t => t ◇ q1) (p24 q0 q1)))).symm
  have p26 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ q0)) = ((q0 ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((p23 q1 (q1 ◇ q1) q0).symm).trans (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q1 ◇ q1)) (p22 q0 q1))).symm).trans (p25 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1))).symm
  have p27 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q2))) = ((q0 ◇ q1) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => q0 ◇ t) (p26 q1 q2)).symm).trans ((((p21 q0 (q2 ◇ q1)).symm).trans (p23 (q0 ◇ q0) q1 q2)).trans ((cg (fun t => t ◇ q1) (p21 q0 q2)).trans (p23 q1 (q2 ◇ q2) q0)))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ ((z ◇ (y ◇ z)) ◇ y)):=(((((cg (fun t => (x ◇ y) ◇ t) (cg (fun t => t ◇ y) (p1v y z))).trans (cg (fun t => (x ◇ y) ◇ t) (p23 y (y ◇ y) y))).trans (p27 (x ◇ y) y y)).trans (p23 (y ◇ y) y (x ◇ y))).trans (p25 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19010_to_19756 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19010_to_19756
