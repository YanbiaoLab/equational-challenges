-- Equation19023 → Equation58584
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
-- Conclusion: (x ◇ y) ◇ y = y ◇ (x ◇ (x ◇ y))
-- Original submission SHA-256: aaad38fbc76cb55c50be2077b16288b9642adcc5e4b27988912bf50aad55e9cd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ y = y ◇ (x ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) ((h b (b ◇ a) a).symm)).symm).trans ((h (a ◇ (b ◇ a)) b (b ◇ a)).symm)
  have p1:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm))).symm).trans (p0 (a ◇ a) (a ◇ a))
  have p2:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a a a)
  have p3:=fun (a:G)=>by
    exact ((p2 a a a).symm).trans ((h a a a).symm)
  have p4:=fun (a:G)=>by
    exact (p1 a).trans (p3 a)
  have p5:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ (b ◇ a)) ◇ (((c ◇ b) ◇ (a ◇ c)) ◇ d))) ((h a b c).symm)).symm).trans ((h ((c ◇ b) ◇ (a ◇ c)) (b ◇ a) d).symm)
  have p6:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p4 a)))).symm).trans (p0 (a ◇ a) ((a ◇ a) ◇ a))).trans (cg (fun t => (a ◇ a) ◇ t) (p4 a))
  have p7:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p0 a b)))).symm).trans (p0 b (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => b ◇ t) (p0 a b))
  have p8:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) (cg (fun t => t ◇ (d ◇ (b ◇ a))) ((h a b c).symm))).symm).trans ((h d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a)).symm)
  have p9:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p6 a)))).symm).trans (p0 ((a ◇ a) ◇ a) (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p6 a))
  have pa:=fun (a:G)=>by
    exact (((p3 ((a ◇ a) ◇ a)).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))) (p9 a)).symm).trans (p4 (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))))).symm
  have pb:=fun (a b c d:G)=>by
    exact ((cg (fun t => (d ◇ (b ◇ a)) ◇ t) (cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) ((h a b c).symm))).symm).trans ((h (b ◇ a) d ((c ◇ b) ◇ (a ◇ c))).symm)
  have pc:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p7 a b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p7 a b)).symm).trans (pa (b ◇ (a ◇ (b ◇ a))))).trans (p7 a b))
  have pd:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4 a))).symm).trans ((h b (a ◇ a) ((a ◇ a) ◇ a)).symm)
  have pe:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pa a))).symm).trans (pd a ((a ◇ a) ◇ a))
  have pf:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ c))) (p0 a b)).symm).trans ((h b (b ◇ (a ◇ (b ◇ a))) c).symm)
  have pg:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ b))) (p4 a)).symm).trans ((h (a ◇ a) ((a ◇ a) ◇ a) b).symm)
  have ph:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pa a))).symm).trans (pg a ((a ◇ a) ◇ a))
  have pi:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (pa a))).symm).trans ((h b ((a ◇ a) ◇ a) ((a ◇ a) ◇ a)).symm)
  have pj:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (b ◇ a))))) (pc a b))).symm).trans (pf a b (b ◇ (a ◇ (b ◇ a))))
  have pk:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (c ◇ (a ◇ (c ◇ a)))) ◇ t) (cg (fun t => (c ◇ b) ◇ t) (p0 a c))).symm).trans ((h (c ◇ (a ◇ (c ◇ a))) b c).symm)
  have pl:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4 a))).symm).trans ((h ((a ◇ a) ◇ a) b (a ◇ a)).symm)
  have pm:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p3 a))).symm).trans (pl a ((a ◇ a) ◇ (a ◇ a)))
  have pn:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) (pa a)).symm).trans (pl a ((a ◇ a) ◇ a))
  have po:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a)))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (pa a)))).trans (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (pa a))).symm).trans ((((cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pl a ((a ◇ a) ◇ a)))).symm).trans (pl ((a ◇ a) ◇ a) (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a))).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a)).trans (pa a)))
  have pp:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)))) (p3 (a ◇ a))).symm).trans (p8 a a a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))
  have pq:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (pa a))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (po a))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (po a)))).symm).trans (p0 ((a ◇ a) ◇ a) ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)))).trans ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (po a)).trans (pa a)))
  have pr:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pn a)).trans (pa a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) ◇ t) (pq a)).symm).trans (pi a (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)))).symm
  have ps:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pe a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pr a)))).symm).trans (p0 a ((a ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => a ◇ t) (pr a)))
  have pt:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (ps a)).symm).trans (ph a)
  have pu:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ (a ◇ (a ◇ a))))) (pr a)).symm).trans (p8 (a ◇ a) a a a)
  have pv:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ t) (pt b)).symm).trans (p8 b (b ◇ b) a b)
  have pw:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (pa a))).symm).trans ((h ((a ◇ a) ◇ a) b ((a ◇ a) ◇ a)).symm)
  have px:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (p0 a ((b ◇ b) ◇ b))).symm).trans (pw b (a ◇ (((b ◇ b) ◇ b) ◇ a)))
  have py:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm)))).symm).trans (pu (a ◇ a))
  have pz:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ t) (pm a)).symm).trans (pl (a ◇ a) ((a ◇ a) ◇ a))
  have p10:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b)) ◇ a) ◇ t) (pd a a)).symm).trans (p8 ((a ◇ a) ◇ a) a b a)
  have p11:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (py a)))).trans (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p4 a)))).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)))) (pm a)))).symm).trans (p10 (a ◇ a) (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a))))
  have p12:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) ((h a a a).symm)).symm).trans (p11 (a ◇ a))
  have p13:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (pm a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p12 a)))).symm).trans (pv a (a ◇ a)))
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (p11 a))).symm).trans ((h b (a ◇ a) (a ◇ (a ◇ a))).symm)
  have p15:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p12 b))).symm).trans ((h a ((b ◇ b) ◇ (b ◇ b)) b).symm)
  have p16:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ b))) (p11 a)).symm).trans ((h (a ◇ a) (a ◇ (a ◇ a)) b).symm)
  have p17:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (p3 a))).symm).trans (p16 a ((a ◇ a) ◇ (a ◇ a)))
  have p18:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p11 a))).symm).trans ((h (a ◇ (a ◇ a)) b (a ◇ a)).symm)
  have p19:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p3 a))).symm).trans (p18 a ((a ◇ a) ◇ (a ◇ a)))
  have p1a:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b))) (p12 a)).symm).trans ((h ((a ◇ a) ◇ (a ◇ a)) a b).symm)
  have p1b:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a))).symm).trans (p8 (a ◇ a) (a ◇ a) b (a ◇ a))
  have p1c:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (pv (a ◇ a) a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p11 a))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ a)) ◇ t) (p17 a)))).symm).trans (p1b a ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ a)))
  have p1d:=fun (a:G)=>by
    exact (((p4 a).symm).trans (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1c a)).symm).trans (ps a))).symm
  have p1e:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1d a))).symm).trans (pi a a)
  have p1f:=fun (a:G)=>by
    exact ((((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) (p1e a))).trans (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p1e a)))).symm).trans (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)))) (p1e a)).symm).trans (p3 (((a ◇ a) ◇ a) ◇ a)))).symm
  have p1g:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (p1f a)).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1f a))).symm).trans (p1e a)
  have p1h:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a)).symm).trans (((cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p1f a)).symm).trans (pl a a))).symm
  have p1i:=fun (a:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a))).trans (pa a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1h (a ◇ a)))).symm).trans (pz a))).symm
  have p1j:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p1c a))).symm).trans (pd a (a ◇ a))
  have p1k:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1j a)).symm).trans (p19 a)
  have p1l:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) ((h a a a).symm)).symm).trans (p1k (a ◇ a))).trans (p3 a)
  have p1m:=fun (a:G)=>by
    exact (((p1k a).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1l (a ◇ a)))).symm).trans (pp a))).symm
  have p1n:=fun (a:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (p1m a))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1m a)))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1g a))).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))) (p1m a)).symm).trans (p3 ((a ◇ a) ◇ (a ◇ a))))
  have p1o:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a)))) (p1g a)).symm).trans (p1c (a ◇ (a ◇ a)))).trans (p1g a))
  have p1p:=fun (a:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (p1g a))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => a ◇ t) (p1g a)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).symm).trans (p13 (a ◇ (a ◇ a)))).trans (p1g a))
  have p1q:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (p1h a)).symm).trans (p1c a)
  have p1r:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1g a))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (p1k a)).symm).trans (p14 a (a ◇ (a ◇ a))))
  have p1s:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).symm).trans (p1d (a ◇ (a ◇ a)))
  have p1t:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (pa a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1h (a ◇ a)))).symm).trans (p1a a (a ◇ a)))
  have p1u:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1m a)).symm).trans (p1h ((a ◇ a) ◇ (a ◇ a)))).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1m a))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1j a))).trans (p1i a))
  have p1v:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1i a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (p1m a)).symm).trans (p13 (a ◇ a)))
  have p1w:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1h a)).symm).trans (p1v a)
  have p1x:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p1m a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (p1l a))).symm).trans (p1a a ((a ◇ a) ◇ (a ◇ a))))
  have p1y:=fun (a b c d e:G)=>by
    exact ((cg (fun t => (((c ◇ (a ◇ e)) ◇ (((b ◇ a) ◇ (e ◇ b)) ◇ c)) ◇ d) ◇ t) (cg (fun t => t ◇ (d ◇ e)) (p5 e a b c))).symm).trans ((h d ((c ◇ (a ◇ e)) ◇ (((b ◇ a) ◇ (e ◇ b)) ◇ c)) e).symm)
  have p1z:=fun (a b c d e:G)=>by
    exact ((cg (fun t => (e ◇ d) ◇ t) (cg (fun t => (((c ◇ (a ◇ d)) ◇ (((b ◇ a) ◇ (d ◇ b)) ◇ c)) ◇ e) ◇ t) (p5 d a b c))).symm).trans ((h d e ((c ◇ (a ◇ d)) ◇ (((b ◇ a) ◇ (d ◇ b)) ◇ c))).symm)
  have p20:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1h a)).symm).trans (pa a)
  have p21:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1d b))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have p22:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b))) (p1d a)).symm).trans ((h ((a ◇ a) ◇ a) a b).symm)
  have p23:=fun (a b:G)=>by
    exact ((((((((cg (fun t => t ◇ (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) (cg (fun t => a ◇ t) (p1f a)))))).trans (cg (fun t => t ◇ (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1f a))))))).trans (cg (fun t => ((((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => a ◇ t) (p1f a)))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p11 a)))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1p a))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (p1d a)))).trans (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p20 a)))).symm).trans (((cg (fun t => t ◇ (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (px a a)))).symm).trans (p1y (((a ◇ a) ◇ a) ◇ a) a (a ◇ (((a ◇ a) ◇ a) ◇ a)) b (a ◇ a)))
  have p24:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ (b ◇ b)))) (p1l b))).symm).trans ((h a b ((b ◇ b) ◇ (b ◇ b))).symm)
  have p25:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) ◇ t) (p1q a)).symm).trans (p8 (a ◇ a) a b a)
  have p26:=fun (a b:G)=>by
    exact ((((((((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) (cg (fun t => a ◇ t) (p1f a))))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1f a)))))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p11 a))))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => ((((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => a ◇ t) (p1f a)))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p1p a)))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (p1d a))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p20 a)))).symm).trans (((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (a ◇ a))) ◇ t) (px a a))))).symm).trans (p1z (((a ◇ a) ◇ a) ◇ a) a (a ◇ (((a ◇ a) ◇ a) ◇ a)) (a ◇ a) b))
  have p27:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p1h b))).symm).trans ((h a b (b ◇ b)).symm)
  have p28:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (p1f a)).symm).trans ((h a ((a ◇ a) ◇ a) b).symm)
  have p29:=fun (a b:G)=>by
    exact ((((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a)))).trans (cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ (a ◇ a))))) (cg (fun t => ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ t) (p1g a)))).trans (cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ t) (p1o a))).symm).trans ((((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a)))) (p28 a b))).symm).trans (p26 (a ◇ (a ◇ a)) ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)))).trans (p1g a))
  have p2a:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (p1g a))).symm).trans ((h b (a ◇ (a ◇ a)) (a ◇ (a ◇ a))).symm)
  have p2b:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p3 a)))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))) (cg (fun t => t ◇ b) ((h a a a).symm))).symm).trans (p2a (a ◇ a) b))
  have p2c:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ (((b ◇ (a ◇ a)) ◇ (a ◇ b)) ◇ a)) (p1d a))).symm).trans (p5 a (a ◇ a) b a)
  have p2d:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) ((h b b a).symm))).symm).trans (pg b ((a ◇ b) ◇ (b ◇ a)))
  have p2e:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1n a)))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p1g a))))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (p1u a)))).symm).trans (((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1g a))))).symm).trans (p27 b (a ◇ (a ◇ a))))
  have p2f:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1f b))).symm).trans ((h ((b ◇ b) ◇ b) a b).symm)
  have p2g:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => t ◇ b) ((h b b a).symm))).symm).trans (pl b ((a ◇ b) ◇ (b ◇ a)))
  have p2h:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ b))) (p1g a)).symm).trans ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) b).symm)
  have p2i:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p3 a)))).symm).trans ((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b)) (cg (fun t => b ◇ t) ((h a a a).symm)))).symm).trans (p2h (a ◇ a) b)).trans (p3 a))
  have p2j:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (p1g a))).symm).trans ((h (a ◇ (a ◇ a)) b (a ◇ (a ◇ a))).symm)
  have p2k:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ b) (p3 a)))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b) ◇ (a ◇ a))) (cg (fun t => b ◇ t) ((h a a a).symm))).symm).trans (p2j (a ◇ a) b)).trans (p3 a))
  have p2l:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ (a ◇ b))) (p1n a)).symm).trans ((h a (a ◇ (a ◇ a)) b).symm)
  have p2m:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ ((a ◇ a) ◇ b))) (p1m a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (cg (fun t => b ◇ t) ((h a a a).symm)))).symm).trans (p2l (a ◇ a) b))
  have p2n:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (cg (fun t => t ◇ c) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1d a))))).symm).trans (pb a b ((a ◇ a) ◇ a) c)
  have p2o:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))))))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1w a)))))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p1j a))))).symm).trans ((((cg (fun t => t ◇ (((((((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a))) ◇ b) ◇ (a ◇ (a ◇ a)))) (cg (fun t => b ◇ t) (p1g a))).symm).trans (p2n (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) b)).trans (p1g a))
  have p2p:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (p1c b))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (p2g a b))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p2g a b)))).symm).trans (p0 (b ◇ b) (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)))).trans ((cg (fun t => (b ◇ b) ◇ t) (p2g a b)).trans (p1c b)))
  have p2q:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p2d a b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ b))) (p2p a b)).symm).trans (p21 (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) b))).symm
  have p2r:=fun (a b:G)=>by
    exact ((((cg (fun t => ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (p12 b)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p2i b a))).trans (p12 b)).symm).trans (((cg (fun t => ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p2q a b))).symm).trans (pd b ((a ◇ b) ◇ (b ◇ a))))
  have p2s:=fun (a b c:G)=>by
    exact (((p2r a c).symm).trans (p2r b c)).symm
  have p2t:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p2r a b)).symm).trans (p1l b)
  have p2u:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (p2r a b)).symm).trans (p1h (b ◇ b))).trans (cg (fun t => (b ◇ b) ◇ t) (p3 b))
  have p2v:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1m b)).symm).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b)))) (p2r a b)).symm).trans (p3 (b ◇ b)))
  have p2w:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1m b)).symm).trans ((((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ t) (p2r a b)).symm).trans (p1i (b ◇ b))).trans (p1i b))
  have p2x:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p2r a c)))).symm).trans (p24 b c)
  have p2y:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pa a)).trans (pa a)).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (pa a)).symm).trans (p2r b ((a ◇ a) ◇ a)))).symm
  have p2z:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ (b ◇ a)) ◇ t) ((h a b c).symm)).symm).trans (p2s d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a))
  have p30:=fun (a b c d:G)=>by
    exact ((p2z a b c d).symm).trans (p2z a b c a)
  have p31:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (b ◇ a))))) (p0 a b)).symm).trans ((p2r (b ◇ (a ◇ (b ◇ a))) b).symm)
  have p32:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (pw a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2y a b)))).symm).trans (p0 (((a ◇ a) ◇ a) ◇ b) (b ◇ ((a ◇ a) ◇ a)))).trans (((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p30 a (a ◇ a) ((b ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ b)) b)).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p1f a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a)))))).symm
  have p33:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ b) (p2u c a))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ a)) (p2r c a)))).symm).trans (p32 (a ◇ a) b)).trans ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => b ◇ t) (p1i a))).trans (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p1i a))))
  have p34:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (pv a b)).symm).trans ((p2r (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) (b ◇ b)).symm)).trans (p1m b)
  have p35:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a))) (p25 a b)).symm).trans ((p2r (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) (a ◇ a)).symm)).trans (p1m a)
  have p36:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ a) ◇ (a ◇ b))) ((p2r a b).symm)).symm).trans (p2s c (a ◇ b) (b ◇ a))).trans (p30 a b ((c ◇ (b ◇ a)) ◇ ((b ◇ a) ◇ c)) c)
  have p37:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ ((c ◇ b) ◇ (b ◇ c))) (p2s a b c)).symm).trans (p2s d (b ◇ c) (c ◇ b))).trans (p30 b c ((d ◇ (c ◇ b)) ◇ ((c ◇ b) ◇ d)) d)
  have p38:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ t) (p1l a)).symm).trans (((cg (fun t => ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p25 a b))).symm).trans (p2b (a ◇ a) (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)))
  have p39:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (p10 b a)).symm).trans ((p2r (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b) b).symm)
  have p3a:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p29 b a)).symm).trans ((p2r (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) b).symm)
  have p3b:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) ((p2r b a).symm)).symm).trans (p36 a b a)
  have p3c:=fun (a b c:G)=>by
    exact ((cg (fun t => ((c ◇ c) ◇ (c ◇ c)) ◇ t) (p2s a c b)).symm).trans (p36 b c a)
  have p3d:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((b ◇ d) ◇ (d ◇ b)) ◇ t) (p2s a d c)).symm).trans (p37 b c d a)
  have p3e:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ a) ◇ c) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ b))) ((p2r a b).symm))).symm).trans ((h c (b ◇ a) (a ◇ b)).symm)
  have p3f:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (pd b (a ◇ b)))).symm).trans (pb a b b (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))))
  have p3g:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) ◇ ((b ◇ b) ◇ c))) (pv a b)).symm).trans ((h (b ◇ b) (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) c).symm)
  have p3h:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p34 a b)).trans (p11 b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p3g a b (b ◇ b))).symm).trans (p2x b ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) b))).symm
  have p3i:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ t) (p1i b))))).trans (cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pv a b)))))).trans (cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (p1d b))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) (pv a b)))).trans (cg (fun t => t ◇ (b ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (p4 b))).trans (p2c b a)).symm).trans ((((cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => ((b ◇ b) ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b)))) ◇ t) (p3h a b))).symm).trans (p3f (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) (b ◇ b))).trans (p3h a b))
  have p3j:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (a ◇ b)) ◇ ((b ◇ a) ◇ c))) ((p2r a b).symm)).symm).trans ((h (b ◇ a) (a ◇ b) c).symm)
  have p3k:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ a)) ◇ (b ◇ (a ◇ b))) ◇ t) (p3j a b b)).symm).trans (p3e (b ◇ a) b (b ◇ (a ◇ b)))
  have p3l:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (p1d b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) ◇ t) (p22 b a))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p39 a b))).trans (p1t b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p22 b a)))).symm).trans (p3k ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b))).symm
  have p3m:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p10 b a))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (p1l b))).trans (p3l a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b) ◇ b)) (p3l a b))).symm).trans (p2t b (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)))).symm
  have p3n:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (p3 b)).trans (cg (fun t => t ◇ b) (p22 b a))).trans (p1f b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p3m a b))).symm).trans (p2b b ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))).symm
  have p3o:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1r a))).symm).trans ((h (a ◇ (a ◇ a)) b ((a ◇ a) ◇ a)).symm)
  have p3p:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ ((a ◇ a) ◇ c))) (p25 a b)).symm).trans ((h (a ◇ a) (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) c).symm)
  have p3q:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p35 b a)).trans (p11 b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b))) ◇ t) (p3p b a (b ◇ b))).symm).trans (p2x b ((b ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b)) b))).symm
  have p3r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ a) (p3q b a)).symm).trans (p38 a b)).symm
  have p3s:=fun (a b:G)=>by
    exact (((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (pa b)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p2m b a))).trans (p1c b)).symm).trans (((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3r b a))).symm).trans (p2e b ((a ◇ b) ◇ ((b ◇ b) ◇ a))))).symm
  have p3t:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ b) (p1g a))).symm).trans (p3s b (a ◇ (a ◇ a)))).trans (p1g a)
  have p3u:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ (a ◇ (a ◇ a))))) (p3t a b)).symm).trans ((p2r (b ◇ (a ◇ (a ◇ a))) (a ◇ b)).symm)).trans (p30 b a (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b))) (a ◇ b))).symm
  have p3v:=fun (a b c:G)=>by
    exact (((p3u a c).symm).trans (p2s b c (a ◇ c))).symm
  have p3w:=fun (a b c:G)=>by
    exact (p3v a b c).trans ((p3v a a c).symm)
  have p3x:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (((a ◇ ((c ◇ c) ◇ c)) ◇ (c ◇ a)) ◇ c))) (p29 c a))).symm).trans ((h b c (((a ◇ ((c ◇ c) ◇ c)) ◇ (c ◇ a)) ◇ c)).symm)
  have p3y:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1f b)))).trans (cg (fun t => t ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) (p1o b))).symm).trans ((((cg (fun t => (b ◇ (b ◇ (((b ◇ b) ◇ b) ◇ b))) ◇ t) (p5 b ((b ◇ b) ◇ b) a b)).symm).trans (p3x a (b ◇ (((b ◇ b) ◇ b) ◇ b)) b)).trans (cg (fun t => b ◇ t) (p1f b)))
  have p3z:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p1o b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p3y a b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ b)))) (p3a a b))).trans (p1x b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p3y a b)))).symm).trans (p3k ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) b))).symm
  have p40:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p29 b a))).trans (cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (p1l b))).trans (p3z a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ b)) (p3z a b))).symm).trans (p2t b (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)))).symm
  have p41:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (p3 b)).trans (cg (fun t => t ◇ b) (p3y a b))).trans (p0 b b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p40 a b))).symm).trans (p2b b ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))))).symm
  have p42:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p1i b))))).trans (cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p1m b)))).trans (cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ a))) ◇ t) (p1v b))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (pg b a))).trans (p3 b)).symm).trans ((((cg (fun t => (b ◇ ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p40 a (b ◇ b)))).symm).trans (p23 b ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p1i b))))).symm
  have p43:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (pl b a)).symm).trans ((((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p42 a b)))).symm).trans (p0 ((b ◇ b) ◇ a) (a ◇ ((b ◇ b) ◇ b)))).trans (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p42 a b)))
  have p44:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (p2f a b)).trans (p43 a b)).symm).trans ((((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p41 a b)))).symm).trans (p0 (b ◇ a) (a ◇ ((b ◇ b) ◇ b)))).trans (cg (fun t => (b ◇ a) ◇ t) (p41 a b)))
  have p45:=fun (a b c:G)=>by
    exact (p33 b c a).trans (p43 c b)
  have p46:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ c) (p2r a b))).symm).trans (p44 c (b ◇ b))).trans (cg (fun t => ((b ◇ b) ◇ c) ◇ t) (p3 b))
  have p47:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p43 b a)).symm).trans (pi a b)
  have p48:=fun (a b:G)=>by
    exact ((((p45 ((((b ◇ b) ◇ b) ◇ ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ ((b ◇ b) ◇ b)) b ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))).trans (cg (fun t => t ◇ b) (p16 b a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ b) ◇ ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => t ◇ b) (p16 b a))).symm).trans (p47 b ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))))).symm
  have p49:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (p2i a c))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p2r c a)))).symm).trans (p48 b (a ◇ a))).trans (p1i a))
  have p4a:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p3 b))).symm).trans ((((cg (fun t => (c ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b)))) ◇ t) (cg (fun t => t ◇ c) (p2r a b))).symm).trans (p48 c (b ◇ b))).trans (p1i b))
  have p4b:=fun (a b c:G)=>by
    exact (((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p1r b)))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p3d a a b b))))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1r b))))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (p1g b)))).symm).trans ((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p3d a a b b)))).symm).trans (p49 ((a ◇ b) ◇ (b ◇ a)) c a)).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3d a a b b)).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1r b))).trans (p2w a b)))
  have p4c:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p4b b a b)).symm).trans (((cg (fun t => ((b ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ (a ◇ b)) ◇ t) (p4b a b ((b ◇ a) ◇ (a ◇ b)))).symm).trans (p4a (b ◇ a) (a ◇ b) (b ◇ ((b ◇ a) ◇ (a ◇ b)))))).symm
  have p4d:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p1r b))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p3d a a b b))).symm).trans (p3i c ((a ◇ b) ◇ (b ◇ a)))).trans ((p3d a a b b).trans (p1r b)))
  have p4e:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p3d a c a a)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p1r a))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2r c a))).symm).trans (p3b b (a ◇ a)))).symm
  have p4f:=fun (a b c d:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p3d a d a a)).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p1r a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2r d a))).symm).trans (p3c b c (a ◇ a))).trans (p4e a c ((c ◇ ((a ◇ a) ◇ c)) ◇ (((a ◇ a) ◇ c) ◇ c))))).symm
  have p4g:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ c) ◇ (c ◇ c))) (p2i a d)).symm).trans ((((cg (fun t => t ◇ ((c ◇ c) ◇ (c ◇ c))) (cg (fun t => (a ◇ a) ◇ t) (p2r d a))).symm).trans (p4f (a ◇ a) b c d)).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p3 a)))
  have p4h:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (p1f b))).symm).trans ((((cg (fun t => a ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ b)) (p1d b))).symm).trans ((p4g a b ((b ◇ b) ◇ b) a).symm)).trans (((cg (fun t => a ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ b) ◇ b))) (pa b))).trans (cg (fun t => a ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pa b)))).trans (cg (fun t => a ◇ t) (pa b))))).symm
  have p4i:=fun (a b c d:G)=>by
    exact ((p4g b c d a).symm).trans (p4g b b d a)
  have p4j:=fun (a b:G)=>by
    exact (((cg (fun t => a ◇ t) (p1s b)).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1h b))).symm).trans (p4i a a b (b ◇ b)))).symm
  have p4k:=fun (a b c d:G)=>by
    exact ((p4f b c d a).symm).trans (p4f b b d a)
  have p4l:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p2s a b (c ◇ c))).symm).trans (p4j b c)
  have p4m:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => (((b ◇ b) ◇ a) ◇ c) ◇ t) (p3s a b))).symm).trans ((h (a ◇ b) c ((b ◇ b) ◇ a)).symm)
  have p4n:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ a))) (p1d b))).symm).trans (pk a ((b ◇ b) ◇ b) b)
  have p4o:=fun (a b c:G)=>by
    exact (((p4k ((a ◇ (a ◇ a)) ◇ ((c ◇ c) ◇ (c ◇ c))) a c c).symm).trans (((p4e a c a).symm).trans (p2s b c ((a ◇ a) ◇ c)))).symm
  have p4p:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1r b)))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (p2w a b)))).symm).trans ((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3d a a b b)))).symm).trans (p3n c ((a ◇ b) ◇ (b ◇ a)))).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p3d a a b b)).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1r b))).trans (p2v a b)))
  have p4q:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (p1u a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1m a)))).symm).trans (p41 b ((a ◇ a) ◇ (a ◇ a)))).trans ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1m a)).trans (p1j a)))
  have p4r:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4c ((a ◇ a) ◇ (a ◇ a)) b))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1m a)))))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p1u a))))).trans (cg (fun t => ((((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (p46 a a b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ a)) (p41 ((a ◇ a) ◇ a) b))).symm).trans (((cg (fun t => ((((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ t) (p4q a b))).symm).trans (p21 (b ◇ ((a ◇ a) ◇ a)) (((a ◇ a) ◇ (a ◇ a)) ◇ b)))
  have p4s:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1r b)))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p2w a b)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3d a a b b)))).symm).trans (p41 c ((a ◇ b) ◇ (b ◇ a)))).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p3d a a b b)).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1r b))).trans (p2v a b)))
  have p4t:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ t) (p4c a b))).trans (cg (fun t => t ◇ (b ◇ b)) (p4p b a ((b ◇ b) ◇ b)))).symm).trans (((cg (fun t => ((((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b))) ◇ t) (p4p a b ((b ◇ a) ◇ (a ◇ b)))).symm).trans (p4s (b ◇ a) (a ◇ b) (((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b)))))).symm
  have p4u:=fun (a b:G)=>by
    exact ((((((cg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p4t a b))).trans (p3w (a ◇ a) (a ◇ b) (b ◇ b))).trans (p4o a (a ◇ a) (b ◇ b))).trans (p4l a (a ◇ (a ◇ a)) b)).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b))) (cg (fun t => (a ◇ b) ◇ t) (p4t a b))).symm).trans (p1r (a ◇ b))).trans (cg (fun t => (a ◇ b) ◇ t) (p4t a b)))).symm
  have p4v:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (pc a b))).trans (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (p4n a b))).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4n a b)))).symm).trans (p0 (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))).trans ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4n a b)).trans (pc a b)))
  have p4w:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4n a b)).trans (pc a b)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p4v a b)).symm).trans ((p2r (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))).symm)).trans (((((((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (p4t ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b)))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p4t ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a)))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b)))).trans (p4t ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b))))).symm
  have p4x:=fun (a b:G)=>by
    exact ((((((p4t (b ◇ (a ◇ (b ◇ a))) (b ◇ (b ◇ b))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p1g b))).trans (cg (fun t => t ◇ b) (pc a b))).trans (p0 a b)).symm).trans (((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p4w a b))).symm).trans (p3o b (b ◇ (a ◇ (b ◇ a)))))).symm
  have p4y:=fun (a b c:G)=>by
    exact (((p4x a c).symm).trans (p4x b c)).symm
  have p4z:=fun (a b:G)=>by
    exact (((p3 a).symm).trans (((cg (fun t => (a ◇ a) ◇ t) ((p2r a a).symm)).symm).trans (p4x b (a ◇ a)))).symm
  have p50:=fun (a b:G)=>by
    exact (((((((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4w a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p4w a b)))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p4w a b))).trans (cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (pc a b))).trans (pc a b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p4w a b))).symm).trans (p31 (b ◇ (a ◇ (b ◇ a))) ((b ◇ b) ◇ b))).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ b) ◇ b))) (pa b)).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pa b))).trans (pa b)))
  have p51:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p4x a b)).symm).trans (p1n b)
  have p52:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) ((p4x b a).symm)).symm).trans ((p4x (a ◇ b) b).symm)
  have p53:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p3 a)))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p52 a b))).trans (p1g b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p52 a (a ◇ a))))).symm).trans (p4r (a ◇ (a ◇ a)) b)).trans ((cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1g a))).trans (cg (fun t => b ◇ t) (p50 a a))))).symm
  have p54:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (p50 a a))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p53 a b))).symm).trans (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p4h b a)).symm).trans ((p4x ((a ◇ a) ◇ a) b).symm))
  have p55:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (p52 a b))).trans (cg (fun t => t ◇ b) (p50 b b))).trans (p1f b)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) ((p4x b a).symm)))).symm).trans (p0 (a ◇ b) b))).symm
  have p56:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4z a b)).symm).trans (p55 (a ◇ a) b)
  have p57:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ c) ◇ t) (p4y a c b)).symm).trans ((p4x (b ◇ c) c).symm)
  have p58:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ (c ◇ b))) (p4z a c)).symm).trans (p57 b c ((a ◇ a) ◇ c))).trans (((cg (fun t => ((a ◇ a) ◇ c) ◇ t) (p4t (a ◇ a) c)).trans (p4u (a ◇ a) c)).trans (cg (fun t => t ◇ (c ◇ (c ◇ c))) (p3 a)))).symm
  have p59:=fun (a b c:G)=>by
    exact ((p58 a b c).symm).trans (p58 a a c)
  have p5a:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((c ◇ b) ◇ (a ◇ c)) ◇ t) ((h a b c).symm)).symm).trans (p4y d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a))
  have p5b:=fun (a b c d:G)=>by
    exact ((p5a a b c d).symm).trans (p5a a b c a)
  have p5c:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ a) ◇ t) (p3i a b)).symm).trans (p4y c (b ◇ a) (a ◇ (b ◇ b)))).symm
  have p5d:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (p3 c)).symm).trans (((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (p57 a b (c ◇ c))).symm).trans (p5c b c (a ◇ (b ◇ a))))
  have p5e:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ b) ◇ b) ◇ t) (p4z a b)).symm).trans ((p2r ((a ◇ a) ◇ b) b).symm)
  have p5f:=fun (a b c:G)=>by
    exact (((p12 b).symm).trans ((((cg (fun t => b ◇ t) (p51 c b)).symm).trans (p4y a b (c ◇ (b ◇ c)))).trans (cg (fun t => a ◇ t) (p5d c b a)))).symm
  have p5g:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p53 a b))).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4 a))).symm).trans (p5a b (a ◇ a) ((a ◇ a) ◇ a) c)).trans (p5b b (a ◇ a) (c ◇ (((a ◇ a) ◇ b) ◇ c)) c))).symm
  have p5h:=fun (a b:G)=>by
    exact (((p5g a b a).symm).trans ((p4x b ((a ◇ a) ◇ b)).symm)).trans ((((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4t (a ◇ a) b)).trans (p4u (a ◇ a) b)).trans (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p3 a))).trans (p59 a b b))
  have p5i:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (c ◇ b)) ◇ t) (p4y a (c ◇ (b ◇ (c ◇ b))) c)).symm).trans (pj b c)
  have p5j:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ b)) ◇ t) ((p4x (b ◇ b) a).symm)).symm).trans (p4z b (a ◇ (b ◇ b)))
  have p5k:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (b ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (p3 b))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p5b a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p1d a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ ((a ◇ a) ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p5j (b ◇ b) a))).symm).trans (p4m (a ◇ a) b ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b)))))
  have p5l:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p3 a)).symm).trans (((cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) ((p2r a a).symm))).symm).trans (p5j (a ◇ a) b))
  have p5m:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ (((c ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ c)) ◇ b)) (cg (fun t => b ◇ t) (p1l a))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p3w a c a)))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p1r a)))).trans (cg (fun t => (b ◇ a) ◇ t) (p5d a a b))).trans (p5k (b ◇ a) b)).symm).trans ((((cg (fun t => t ◇ (((c ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ c)) ◇ b)) (cg (fun t => b ◇ t) (p5k (a ◇ a) a))).symm).trans (p4d c (a ◇ a) b)).trans (p3 a))
  have p5n:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p53 (b ◇ a) b))).symm).trans (((cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a))))) (p5m a b a)).symm).trans (pd (b ◇ a) b))
  have p5o:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ b))) (cg (fun t => a ◇ t) (p53 a b))).trans (cg (fun t => (a ◇ b) ◇ t) (p5b a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => (a ◇ b) ◇ t) (p1d a))).symm).trans (((cg (fun t => (a ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (pd a b))).symm).trans (p5n (a ◇ (b ◇ ((a ◇ a) ◇ a))) ((a ◇ a) ◇ b)))
  have p5p:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => b ◇ t) (p2b a b))).symm).trans (((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => t ◇ ((a ◇ b) ◇ ((a ◇ a) ◇ (b ◇ a)))) (p2b a b))).symm).trans (p5m ((a ◇ a) ◇ (b ◇ a)) (a ◇ b) a))
  have p5q:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => a ◇ t) (p2k a b))).symm).trans (((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ ((b ◇ a) ◇ ((a ◇ b) ◇ (a ◇ a)))) (p2k a b))).symm).trans (p5m ((a ◇ b) ◇ (a ◇ a)) (b ◇ a) a))).symm
  have p5r:=fun (a b c:G)=>by
    exact ((p5o (b ◇ b) a).symm).trans ((((cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p3s a b)).symm).trans (p4y c ((b ◇ b) ◇ a) (a ◇ b))).trans (p5b b a (c ◇ ((a ◇ b) ◇ c)) c))
  have p5s:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ b) (p3d a c a a)).trans (cg (fun t => t ◇ b) (p1r a))).trans (p5d a a b)).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p2r c a))).symm).trans (p5r b (a ◇ a) c)).trans ((p5c b a (a ◇ a)).trans (p5q a b)))
  have p5t:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (p5g b a (a ◇ (((b ◇ b) ◇ a) ◇ a)))).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (p5r (b ◇ b) a a)).symm).trans (p5l (a ◇ a) b))
  have p5u:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ a)) (p5t a b)).symm).trans (p5h ((b ◇ a) ◇ a) (a ◇ a))).trans ((cg (fun t => ((b ◇ a) ◇ a) ◇ t) (p5b a a (((b ◇ a) ◇ a) ◇ ((a ◇ a) ◇ ((b ◇ a) ◇ a))) ((b ◇ a) ◇ a))).trans (cg (fun t => ((b ◇ a) ◇ a) ◇ t) (p1d a)))).symm
  have p5v:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p5l b a))).symm).trans (p5t b ((b ◇ b) ◇ (a ◇ a)))).symm
  have p5w:=fun (a b c:G)=>by
    exact (p5d a b c).trans (p5s b c ((c ◇ b) ◇ (c ◇ c)))
  have p5x:=fun (a b c:G)=>by
    exact ((((((cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p5w c a b)).trans (p4t (a ◇ a) (b ◇ a))).trans (p5r ((b ◇ a) ◇ (b ◇ a)) a (((a ◇ a) ◇ (a ◇ a)) ◇ ((b ◇ a) ◇ (b ◇ a))))).trans (p5g (b ◇ a) a (a ◇ ((((b ◇ a) ◇ (b ◇ a)) ◇ a) ◇ a)))).trans (p5u a b)).symm).trans ((((cg (fun t => t ◇ ((c ◇ (a ◇ c)) ◇ b)) (p5w c a b)).symm).trans (p4t (c ◇ (a ◇ c)) b)).trans (cg (fun t => t ◇ (b ◇ b)) (p5i c c a)))
  have p5y:=fun (a b:G)=>by
    exact (((((cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (cg (fun t => t ◇ a) (p1m a)))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p1n a)))).trans (cg (fun t => a ◇ t) (p1l a))).symm).trans ((((p5r (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) a a).symm).trans (p4x b ((a ◇ a) ◇ (a ◇ a)))).trans (cg (fun t => b ◇ t) (p5r b a (((a ◇ a) ◇ (a ◇ a)) ◇ b))))).symm
  have p5z:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ (b ◇ b)) ◇ t) (p5b b b ((b ◇ a) ◇ ((b ◇ b) ◇ (b ◇ a))) (b ◇ a))).trans (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (p1d b))).symm).trans (((cg (fun t => (a ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (p3i a b)))).symm).trans (p5y (b ◇ a) (a ◇ (b ◇ b))))
  have p60:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ b) (p5m a b a))).symm).trans (p5t b ((b ◇ a) ◇ (b ◇ a)))).symm
  have p61:=fun (a b:G)=>by
    exact (((cg (fun t => (a ◇ a) ◇ t) (p5y a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ (a ◇ ((b ◇ a) ◇ a)))) (p5y a b)).symm).trans (p4t b (a ◇ ((b ◇ a) ◇ a)))).trans (cg (fun t => (b ◇ b) ◇ t) (p5i a a (b ◇ a))))).symm
  have p62:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p5n b a)).symm).trans (p5s ((a ◇ b) ◇ a) b a)).trans ((((((((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ a))) (cg (fun t => t ◇ ((a ◇ b) ◇ a)) (p5o a b))).trans (cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ a))) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p5o a b)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p5o a b)))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ◇ t) (p5b a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) ◇ t) (p1d a))).trans (cg (fun t => t ◇ a) (p4t (a ◇ a) b))).trans (cg (fun t => t ◇ a) (p5r (b ◇ b) a (((a ◇ a) ◇ (a ◇ a)) ◇ (b ◇ b))))).trans (cg (fun t => t ◇ a) (p5g b a (a ◇ (((b ◇ b) ◇ a) ◇ a)))))).symm
  have p63:=fun (a b c d:G)=>by
    exact (((p5b a b (c ◇ ((b ◇ a) ◇ c)) c).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (p5i d d a)))).symm).trans (p5c b (d ◇ (a ◇ d)) c)).trans ((cg (fun t => t ◇ ((d ◇ (a ◇ d)) ◇ (d ◇ (a ◇ d)))) (p5w d a b)).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p5i d d a))))).symm
  have p64:=fun (a b c:G)=>by
    exact (((p5g a c a).symm).trans (p4y b c ((a ◇ a) ◇ c))).symm
  have p65:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (p4y a b (c ◇ b))).symm).trans (p5y b c)
  have p66:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p5n c a)))).symm).trans (p65 b ((a ◇ c) ◇ a) c)).trans (((((cg (fun t => t ◇ ((a ◇ c) ◇ a)) (p5o a c)).trans (cg (fun t => ((a ◇ a) ◇ c) ◇ t) (p5o a c))).trans (p4t (a ◇ a) c)).trans (p5r (c ◇ c) a (((a ◇ a) ◇ (a ◇ a)) ◇ (c ◇ c)))).trans (p64 c a a))
  have p67:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (p5v a b)).symm).trans (p56 b (a ◇ a))).trans (p3 a)
  have p68:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ b) ◇ (b ◇ b)) ◇ t) (p4z a b)).symm).trans (p3i ((a ◇ a) ◇ b) b)
  have p69:=fun (a b:G)=>by
    exact ((((((((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a))) ◇ t) (p5r (a ◇ a) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ a)))).trans (cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a))) ◇ t) (p64 a b b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p5r (((b ◇ b) ◇ a) ◇ (a ◇ a)) b (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a)))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p68 b a))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p5b a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p1d a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p68 b a))).symm).trans (p15 (((b ◇ b) ◇ a) ◇ (a ◇ a)) b))).symm
  have p6a:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1g a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ b))) (p52 a b)).symm).trans (p3s (a ◇ b) (a ◇ (a ◇ a)))).trans (p1g a))
  have p6b:=fun (a b c d:G)=>by
    exact ((p5a a b c d).trans ((p5a a b a d).symm)).trans ((cg (fun t => t ◇ a) (p5q a b)).trans (p63 a b (((a ◇ a) ◇ (b ◇ a)) ◇ a) (((a ◇ a) ◇ (b ◇ a)) ◇ a)))
  have p6c:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ (b ◇ b)))) (p5r (a ◇ b) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ b)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (p62 b a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (p5x a b (b ◇ (a ◇ a)))))).trans (p66 (a ◇ (b ◇ b)) (b ◇ b) (b ◇ (a ◇ (b ◇ b))))).trans (p62 (a ◇ (b ◇ b)) b)).symm).trans (((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ b)) ◇ t) (p6b (b ◇ b) a (b ◇ b) a)).symm).trans (p4m a b ((b ◇ b) ◇ (b ◇ b))))
  have p6d:=fun (a b c d:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (c ◇ b)) ◇ t) (p4z a (c ◇ b))).symm).trans ((p5a b c d ((a ◇ a) ◇ (c ◇ b))).symm)).trans (p6b b c d (((d ◇ c) ◇ (b ◇ d)) ◇ b))
  have p6e:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p5q b c)).symm).trans (((p5f b c a).trans ((p5f c c a).symm)).trans (p12 c))
  have p6f:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (p5v (a ◇ a) b)).trans (cg (fun t => b ◇ t) (p69 b a))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p5e b a))).symm).trans (p6e a b (((b ◇ b) ◇ a) ◇ a))).trans ((((((((((((((((((cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (p4t ((b ◇ b) ◇ a) a)).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p4t (b ◇ b) a)))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p5r (a ◇ a) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ a)))))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ a) ◇ a) ◇ (((b ◇ b) ◇ a) ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (p64 a b b)))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (p4t ((b ◇ b) ◇ a) a))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p4t (b ◇ b) a)))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p5r (a ◇ a) b (((b ◇ b) ◇ (b ◇ b)) ◇ (a ◇ a)))))).trans (cg (fun t => (((a ◇ b) ◇ b) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p64 a b b)))).trans (p4t ((a ◇ b) ◇ b) (a ◇ a))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p4t (a ◇ b) b))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p4t a b)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p6c (a ◇ a) b))).trans (p5q (a ◇ a) b)).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p5x a b (b ◇ (a ◇ a))))).trans (p5r (a ◇ (b ◇ b)) a (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (b ◇ b))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p5o a (b ◇ b))))).trans (cg (fun t => a ◇ t) (p6d a b b (((a ◇ a) ◇ (b ◇ b)) ◇ a)))).trans (cg (fun t => a ◇ t) (p1d b))))
  have p6g:=fun (a b:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p5x a b (b ◇ (a ◇ a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (p5x a b (b ◇ (a ◇ a)))))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p60 (b ◇ b) a))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p69 a b))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p6f b a)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p5x a (b ◇ (a ◇ a)) a))).symm).trans (p6f (a ◇ a) b))
  have p6h:=fun (a b c:G)=>by
    exact ((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ a) (p5w c a a)))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1l a)))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p66 a c (c ◇ (a ◇ c))))).symm).trans (p5k b (c ◇ (a ◇ c)))).trans (p66 a c (b ◇ b)))).symm
  have p6i:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p5n b a))).symm).trans (p6g ((a ◇ b) ◇ a) b)).trans (((((cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ b) ◇ a)) (p5o a b))).trans (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p5o a b)))).trans (cg (fun t => t ◇ b) (p4t (a ◇ a) b))).trans (cg (fun t => t ◇ b) (p5r (b ◇ b) a (((a ◇ a) ◇ (a ◇ a)) ◇ (b ◇ b))))).trans (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p6h a b (((b ◇ b) ◇ a) ◇ a)))))).symm
  have p6j:=fun (a b:G)=>by
    exact ((p66 a a ((a ◇ b) ◇ b)).symm).trans (((cg (fun t => ((a ◇ b) ◇ b) ◇ t) ((p4x b a).symm)).symm).trans ((p2r (a ◇ b) b).symm))
  have p6k:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ b) (p5r (b ◇ b) a (((a ◇ a) ◇ (a ◇ a)) ◇ (b ◇ b)))).trans (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p6h a b (((b ◇ b) ◇ a) ◇ a))))).trans (p6i a b)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ b)) (p6j b a))).symm).trans (p67 (((b ◇ a) ◇ a) ◇ b) b))).symm
  have p6l:=fun (a b c:G)=>by
    exact (((((p66 a a ((a ◇ c) ◇ c)).trans (cg (fun t => t ◇ a) (p6k c a))).trans (p5o a (a ◇ c))).symm).trans (((cg (fun t => ((a ◇ c) ◇ c) ◇ t) ((p4x c a).symm)).symm).trans (p2s b (a ◇ c) c))).symm
  have p6m:=fun (a b c:G)=>by
    exact (((p6l a b c).symm).trans (p6l b b c)).symm
  have p6n:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ c) ◇ t) (p6m a b c)).symm).trans ((p4x (b ◇ c) (b ◇ b)).symm)).trans (p3 b)
  have p6o:=fun (a b c:G)=>by
    exact ((((((cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p61 a b)).trans (p5q (a ◇ a) (b ◇ a))).trans (p5r ((b ◇ a) ◇ (a ◇ a)) a (((a ◇ a) ◇ (a ◇ a)) ◇ ((b ◇ a) ◇ (a ◇ a))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p67 b a)))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ a))) (p5s a b a)).symm).trans (p6l c (b ◇ a) (b ◇ b))).trans (cg (fun t => (c ◇ c) ◇ t) (p5x b c (c ◇ (b ◇ b)))))).symm
  have p6p:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ a)) (cg (fun t => b ◇ t) (p5t a b))).symm).trans (((cg (fun t => t ◇ ((b ◇ a) ◇ a)) (cg (fun t => t ◇ (((b ◇ a) ◇ a) ◇ (a ◇ a))) (p5t a b))).symm).trans (p5m (a ◇ a) ((b ◇ a) ◇ a) a))
  have p6q:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ b) (p60 (b ◇ a) b))).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p67 (b ◇ a) b))).trans (p5w b a (b ◇ a))).symm).trans (((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ b) (p5z (b ◇ a) b))).symm).trans (pb b a b b))
  have p6r:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ c))) (p4x a c)).symm).trans (p6a b c)
  have p6s:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (p66 a a (b ◇ b))).trans (cg (fun t => (c ◇ (a ◇ b)) ◇ t) (p6h a b (((b ◇ b) ◇ a) ◇ a)))).symm).trans (((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) ((p4x b a).symm))).symm).trans (p6n b c (a ◇ b)))
  have p6t:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ c) (p5v (a ◇ a) c)).trans (cg (fun t => t ◇ c) (p69 c a))).trans (p5o c ((c ◇ a) ◇ a))).trans (p6p a c)).symm).trans ((((cg (fun t => t ◇ c) (cg (fun t => (c ◇ c) ◇ t) (p5e b a))).symm).trans (p6d c b (((b ◇ b) ◇ a) ◇ a) a)).trans (((((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ b) (p6h a b (((b ◇ b) ◇ a) ◇ a))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p5o b (b ◇ a))))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p61 a b)))).trans (cg (fun t => b ◇ t) (p5r b a (((a ◇ a) ◇ (a ◇ a)) ◇ b)))).trans (p66 (b ◇ a) a b)))).symm
  have p6u:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ (c ◇ c)) (p5o c ((a ◇ c) ◇ c))).trans (cg (fun t => t ◇ (c ◇ c)) (p6q c a))).trans (p5s a c ((c ◇ a) ◇ (c ◇ c)))).symm).trans (((cg (fun t => t ◇ (c ◇ c)) (cg (fun t => t ◇ c) (p6b c a b a))).symm).trans (p5t c ((b ◇ a) ◇ (c ◇ b))))).symm
  have p6v:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (c ◇ ((b ◇ a) ◇ a))) (p5t a b)).symm).trans (p6u (a ◇ a) ((b ◇ a) ◇ a) c)).trans (((((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p5x a c (c ◇ (a ◇ a)))).trans (p5r (a ◇ (c ◇ c)) a (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (c ◇ c))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (p5o a (c ◇ c))))).trans (cg (fun t => a ◇ t) (p6d a c c (((a ◇ a) ◇ (c ◇ c)) ◇ a)))).trans (cg (fun t => a ◇ t) (p1d c)))
  have p6w:=fun (a b c:G)=>by
    exact ((((((cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p5x a b (b ◇ (a ◇ a))))))).trans (cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (p5x a b (b ◇ (a ◇ a)))))))).trans (cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (cg (fun t => a ◇ t) (p60 (b ◇ b) a))))).trans (cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (cg (fun t => a ◇ t) (p69 a b))))).trans (cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (p6v b a a)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (p5x a (b ◇ (a ◇ a)) a))).symm).trans (p6v (a ◇ a) b c))
  have p6x:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (p5x a c (c ◇ (a ◇ a)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (p6t a b a))).symm).trans (p6v (b ◇ a) b c))
  have p6y:=fun (a b c:G)=>by
    exact ((((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p1g a))).symm).trans (p6x b c (a ◇ (a ◇ a)))).trans (p66 a a (c ◇ b))).symm
  have p6z:=fun (a b c:G)=>by
    exact (((p6c (c ◇ b) a).symm).trans (p6y (a ◇ a) b c)).trans ((cg (fun t => c ◇ t) (p5x a b (b ◇ (a ◇ a)))).trans (p6x a c b))
  have p70:=fun (a b c d:G)=>by
    exact ((((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => c ◇ t) ((h a b d).symm))).symm).trans (p6w ((d ◇ b) ◇ (a ◇ d)) (b ◇ a) c)).trans ((((((((cg (fun t => t ◇ c) (cg (fun t => t ◇ ((d ◇ b) ◇ (a ◇ d))) (p6u b d a))).trans (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((d ◇ b) ◇ (a ◇ d))) (p5p a b)))).trans (cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p6u b d a)))).trans (cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p5p a b)))).trans (cg (fun t => t ◇ c) (p4t (a ◇ a) (b ◇ a)))).trans (cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p60 a b)))).trans (cg (fun t => t ◇ c) (p5r ((a ◇ b) ◇ (b ◇ b)) a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ b)))))).trans (p6z c ((((a ◇ b) ◇ (b ◇ b)) ◇ a) ◇ a) a))).symm
  have p71:=fun (a b c:G)=>by
    exact ((((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => c ◇ t) (p2b a b))).symm).trans (p6w ((a ◇ a) ◇ (b ◇ a)) (a ◇ b) c)).trans (((((cg (fun t => t ◇ c) (p4t (a ◇ a) (b ◇ a))).trans (cg (fun t => t ◇ c) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p60 a b)))).trans (cg (fun t => t ◇ c) (p5r ((a ◇ b) ◇ (b ◇ b)) a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ b)))))).trans (p6z c ((((a ◇ b) ◇ (b ◇ b)) ◇ a) ◇ a) a)).trans (p70 a b c ((a ◇ c) ◇ ((((a ◇ b) ◇ (b ◇ b)) ◇ a) ◇ a))))).symm
  have p72:=fun (a b c:G)=>by
    exact ((((((cg (fun t => c ◇ t) (p5x (a ◇ a) b (b ◇ ((a ◇ a) ◇ (a ◇ a))))).trans (p6x (a ◇ a) c b)).trans (cg (fun t => t ◇ b) (p5x a c (c ◇ (a ◇ a))))).trans (p6z b (c ◇ c) a)).symm).trans (((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) ((p2r a a).symm))).symm).trans (p6x b c (a ◇ a)))).symm
  have p73:=fun (a b c:G)=>by
    exact (((p66 a c (b ◇ a)).symm).trans ((((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => t ◇ c) (p2o a b)))).symm).trans (p65 c (((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a))) (b ◇ a))).trans (((((((((((((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a)))) (p66 a a ((a ◇ a) ◇ b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a)))) (cg (fun t => t ◇ a) (p6z a b (a ◇ a))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a)))) (cg (fun t => t ◇ a) (p54 a b)))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a)))) (p6z a (b ◇ b) b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a)))) (p6u a b b))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p66 a a ((a ◇ a) ◇ b)))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p6z a b (a ◇ a))))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p54 a b)))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p6z a (b ◇ b) b))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ a)) ◇ t) (p6u a b b))).trans (p4t (a ◇ a) (b ◇ a))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p71 a b b))).trans (p6x (a ◇ b) ((a ◇ a) ◇ (a ◇ a)) b)))).symm
  have p74:=fun (a b c:G)=>by
    exact (((p6z a c c).symm).trans ((((cg (fun t => (c ◇ c) ◇ t) (p5t c a)).symm).trans (p6o b ((a ◇ c) ◇ c) c)).trans ((cg (fun t => b ◇ t) (p6z b c (a ◇ c))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ c) (p6z b c a)))))).symm
  have p75:=fun (a b c:G)=>by
    exact (((p5x (a ◇ a) c (c ◇ ((a ◇ a) ◇ (a ◇ a)))).symm).trans ((((cg (fun t => c ◇ t) (p6j c a)).symm).trans (p4y b c (((c ◇ a) ◇ a) ◇ c))).trans ((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p6k a c))).trans (cg (fun t => b ◇ t) (p6z b (c ◇ a) c))))).symm
  have p76:=fun (a b c:G)=>by
    exact (((((((cg (fun t => c ◇ t) (p6z b c ((a ◇ a) ◇ b))).trans (p5b b ((a ◇ a) ◇ b) (c ◇ ((((a ◇ a) ◇ b) ◇ b) ◇ c)) c)).trans (p74 (a ◇ a) b b)).trans (cg (fun t => t ◇ b) (p5x a b (b ◇ (a ◇ a))))).trans (p6z b (b ◇ b) a)).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => (((a ◇ a) ◇ b) ◇ c) ◇ t) (pd a b))).symm).trans (p75 (a ◇ (b ◇ ((a ◇ a) ◇ a))) c ((a ◇ a) ◇ b))).trans (((((((((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b))) (cg (fun t => t ◇ (a ◇ (b ◇ ((a ◇ a) ◇ a)))) (cg (fun t => a ◇ t) (p53 a b)))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b))) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => a ◇ t) (p53 a b))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b))) (p4t a b))).trans (cg (fun t => ((a ◇ a) ◇ (b ◇ b)) ◇ t) (p4t (a ◇ a) b))).trans (p6x ((a ◇ a) ◇ (a ◇ a)) ((a ◇ a) ◇ (b ◇ b)) b)).trans (cg (fun t => t ◇ b) (p5q (a ◇ a) (b ◇ b)))).trans (cg (fun t => t ◇ b) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p72 a b b)))).trans (cg (fun t => t ◇ b) (p6x (a ◇ b) ((a ◇ a) ◇ (a ◇ a)) b))).trans (cg (fun t => t ◇ b) (p73 a b ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ b)) ◇ b)))))).symm
  have p77:=fun (a b c:G)=>by
    exact ((((((((cg (fun t => t ◇ (c ◇ (c ◇ b))) (cg (fun t => (a ◇ (b ◇ c)) ◇ t) (p4t b c))).trans (cg (fun t => t ◇ (c ◇ (c ◇ b))) (p6x (b ◇ b) (a ◇ (b ◇ c)) c))).trans (cg (fun t => t ◇ (c ◇ (c ◇ b))) (cg (fun t => t ◇ c) (p6z (b ◇ b) (b ◇ c) a)))).trans (p6z (c ◇ (c ◇ b)) c ((a ◇ (b ◇ b)) ◇ (b ◇ c)))).trans (cg (fun t => t ◇ c) (p6s b c (a ◇ (b ◇ b))))).trans (p6z c (b ◇ b) a)).symm).trans ((((cg (fun t => t ◇ (c ◇ (c ◇ b))) (p76 a (b ◇ c) a)).symm).trans (p6s b c ((((b ◇ c) ◇ a) ◇ a) ◇ a))).trans (((cg (fun t => t ◇ a) (cg (fun t => t ◇ a) (p6z a c b))).trans (cg (fun t => t ◇ a) (p6z a c (b ◇ a)))).trans (p6z a c ((b ◇ a) ◇ a))))).symm
  have p78:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (p72 a b b))).trans (cg (fun t => t ◇ c) (p67 a b))).symm).trans ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (p77 b a b))).symm).trans (p77 b ((a ◇ b) ◇ b) c)).trans (((cg (fun t => (b ◇ c) ◇ t) (p4t (a ◇ b) b)).trans (cg (fun t => (b ◇ c) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p4t a b)))).trans (cg (fun t => (b ◇ c) ◇ t) (p6c (a ◇ a) b))))).symm
  have p79:=fun (a b c d:G)=>by
    exact ((((((cg (fun t => a ◇ t) (p66 b d (c ◇ c))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ b) (p6z b c c)))).trans (cg (fun t => a ◇ t) (p6z b c (c ◇ b)))).trans (cg (fun t => a ◇ t) (p6k b c))).symm).trans (((cg (fun t => t ◇ ((c ◇ c) ◇ (d ◇ (b ◇ d)))) (p6r d a b)).symm).trans (p78 c (d ◇ (b ◇ d)) (a ◇ (a ◇ b))))).symm
  exact (calc
    ((x ◇ y) ◇ y)=((x ◇ y) ◇ y):=rfl
    _=(y ◇ (x ◇ (x ◇ y))):=((p79 x y y (y ◇ (x ◇ (x ◇ y)))).trans (p66 y y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19023_to_58584 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19023_to_58584
