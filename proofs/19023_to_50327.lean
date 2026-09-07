-- Equation19023 → Equation50327
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
-- Conclusion: x ◇ x = (x ◇ ((y ◇ y) ◇ y)) ◇ x
-- Original submission SHA-256: b559247da2e1b14ce9145ede6c694211428747e9f894c650baa6a0da10256aed
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (x ◇ ((y ◇ y) ◇ y)) ◇ x
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
  have p1:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a a a)
  have p2:=fun (a b c:G)=>by
    exact ((h a a a).trans (p1 a a a)).symm
  have p3:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (a ◇ a) ◇ t) (p2 a a a))).symm).trans (p0 (a ◇ a) (a ◇ a))).trans (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))
  have p4:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p3 a))).symm).trans ((h b (a ◇ a) ((a ◇ a) ◇ a)).symm)
  have p5:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) (cg (fun t => t ◇ (d ◇ (b ◇ a))) ((h a b c).symm))).symm).trans ((h d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a)).symm)
  have p6:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ b))) (p3 a)).symm).trans ((h (a ◇ a) ((a ◇ a) ◇ a) b).symm)
  have p7:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b)) ◇ a) ◇ t) (p4 a a)).symm).trans (p5 ((a ◇ a) ◇ a) a b a)
  have p8:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ a) (cg (fun t => t ◇ a) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p3 a)))).symm).trans (p7 a (a ◇ a))
  have p9:=fun (a b c d:G)=>by
    exact ((cg (fun t => (d ◇ (b ◇ a)) ◇ t) (cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) ((h a b c).symm))).symm).trans ((h (b ◇ a) d ((c ◇ b) ◇ (a ◇ c))).symm)
  have pa:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p3 a))).symm).trans ((h ((a ◇ a) ◇ a) b (a ◇ a)).symm)
  have pb:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ (b ◇ a)) ◇ (((c ◇ b) ◇ (a ◇ c)) ◇ d))) ((h a b c).symm)).symm).trans ((h ((c ◇ b) ◇ (a ◇ c)) (b ◇ a) d).symm)
  have pc:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ c))) (p0 a b)).symm).trans ((h b (b ◇ (a ◇ (b ◇ a))) c).symm)
  have pd:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (c ◇ (a ◇ (c ◇ a))))) (p0 a c))).symm).trans ((h b c (c ◇ (a ◇ (c ◇ a)))).symm)
  have pe:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ c) ◇ (((b ◇ a) ◇ (c ◇ b)) ◇ c)) ◇ t) (p9 c a b c)).symm).trans ((h (((b ◇ a) ◇ (c ◇ b)) ◇ c) (a ◇ c) c).symm)
  have pf:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).symm).trans (p0 (a ◇ a) ((a ◇ a) ◇ a))).trans (cg (fun t => (a ◇ a) ◇ t) (p3 a))
  have pg:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pf a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pf a)))).symm).trans (p8 ((a ◇ a) ◇ a)))
  have ph:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p3 a))).symm).trans (p5 a a b ((a ◇ a) ◇ a))
  have pi:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) ((h b b a).symm))).symm).trans (p6 b ((a ◇ b) ◇ (b ◇ a)))
  have pj:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ b))) (p5 b b a b))).symm).trans (pc b b (((a ◇ b) ◇ (b ◇ a)) ◇ b))
  have pk:=fun (a b:G)=>by
    exact ((cg (fun t => ((((b ◇ b) ◇ (b ◇ a)) ◇ b) ◇ (a ◇ (b ◇ b))) ◇ t) (p3 b)).symm).trans (((cg (fun t => ((((b ◇ b) ◇ (b ◇ a)) ◇ b) ◇ (a ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (pa b (b ◇ a)))).symm).trans (p9 (b ◇ b) a b (((b ◇ b) ◇ (b ◇ a)) ◇ b)))
  have pl:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (c ◇ (a ◇ (c ◇ a)))) ◇ t) (cg (fun t => (c ◇ b) ◇ t) (p0 a c))).symm).trans ((h (c ◇ (a ◇ (c ◇ a))) b c).symm)
  have pm:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pg a))).symm).trans (p6 a ((a ◇ a) ◇ a))
  have pn:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p5 b b a b))).symm).trans (pd b (((a ◇ b) ◇ (b ◇ a)) ◇ b) b)
  have po:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pg a))).symm).trans (p4 a ((a ◇ a) ◇ a))
  have pp:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (ph b a)).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (pi a b))).symm).trans (p0 b (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)))).trans (pi a b))
  have pq:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ ((((b ◇ b) ◇ b) ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p8 b))).symm).trans ((h ((((b ◇ b) ◇ b) ◇ b) ◇ b) a b).symm)
  have pr:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p0 a b)))).symm).trans (p0 b (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => b ◇ t) (p0 a b))
  have ps:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (pr a b)).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (pr a b)))).symm).trans (p8 (b ◇ (a ◇ (b ◇ a)))))
  have pt:=fun (a b c:G)=>by
    exact (((pc a b c).symm).trans (((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (cg (fun t => (c ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ c) ((h b (b ◇ a) a).symm)))).symm).trans (pb (a ◇ (b ◇ a)) b (b ◇ a) c))).symm
  have pu:=fun (a b:G)=>by
    exact (((((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)))) (cg (fun t => (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) (pp b a)))).trans (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)))) (ph a b)))).trans (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pp b a)))).trans (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (p3 a))).symm).trans (((cg (fun t => t ◇ (((((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)))) ◇ (((a ◇ a) ◇ a) ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a))))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pp b a))).symm).trans (pt (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)) ((a ◇ a) ◇ a) b))
  have pv:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (po a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pu a a)))).symm).trans (p0 a ((a ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => a ◇ t) (pu a (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a))))
  have pw:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (pv a)).symm).trans (pm a)
  have px:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ t) (pw b)).symm).trans (p5 b (b ◇ b) a b)
  have py:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((b ◇ b) ◇ b)) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (pw b))).symm).trans ((h a (b ◇ ((b ◇ b) ◇ b)) b).symm)
  have pz:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => ((a ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t) (pw a))).symm).trans ((h a b (a ◇ ((a ◇ a) ◇ a))).symm)
  have p10:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (pp a b))).symm).trans (p0 ((b ◇ b) ◇ b) ((a ◇ b) ◇ (b ◇ a)))).trans (pp a b)
  have p11:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ c) ◇ t) (cg (fun t => t ◇ (c ◇ ((a ◇ a) ◇ b))) (p4 a b))).symm).trans ((h c (a ◇ (b ◇ ((a ◇ a) ◇ a))) ((a ◇ a) ◇ b)).symm)
  have p12:=fun (a b c d e:G)=>by
    exact ((cg (fun t => ((a ◇ (d ◇ (b ◇ a))) ◇ e) ◇ t) (cg (fun t => t ◇ (e ◇ (((c ◇ b) ◇ (a ◇ c)) ◇ d))) (p5 a b c d))).symm).trans ((h e (a ◇ (d ◇ (b ◇ a))) (((c ◇ b) ◇ (a ◇ c)) ◇ d)).symm)
  have p13:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ (a ◇ (b ◇ a))) ◇ (a ◇ (b ◇ a))) ◇ t) (pb a b c a)).symm).trans (p12 a b c a (a ◇ (b ◇ a)))
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b))) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))).symm).trans ((((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm)))).symm).trans (p13 (a ◇ a) (a ◇ a) b)).trans (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))
  have p15:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ a) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ a) (cg (fun t => (a ◇ a) ◇ t) (pb a a a (a ◇ a)))))).trans (cg (fun t => t ◇ a) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) (cg (fun t => t ◇ a) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))))).symm).trans ((((cg (fun t => t ◇ a) (cg (fun t => (((a ◇ a) ◇ (a ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))))) ◇ a) ◇ t) (pu (a ◇ a) a))).symm).trans (pk (((a ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) a)).trans (pu (a ◇ a) ((((a ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ (a ◇ a))))
  have p16:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p3 (a ◇ a))).symm).trans (((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p15 a))).symm).trans (pz (a ◇ a) a))
  have p17:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) ((h a a a).symm)).symm).trans (p16 (a ◇ a))
  have p18:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (ph a a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p17 a)))).symm).trans (px a (a ◇ a)))
  have p19:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p4 b (a ◇ b)))).symm).trans (p9 a b b (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))))
  have p1a:=fun (a:G)=>by
    exact (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pu a (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (pg a)))).symm).trans (((cg (fun t => t ◇ (a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)))) (p19 a a)).symm).trans (p5 a ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a ((a ◇ a) ◇ a)))
  have p1b:=fun (a:G)=>by
    exact (((p3 a).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (p1a a)).symm).trans (p0 a (a ◇ a)))).symm
  have p1c:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (p1b a)).symm).trans (pa a a)
  have p1d:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p8 a)))).symm).trans (((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (p1b a)))))).symm).trans (pj ((a ◇ a) ◇ a) a))
  have p1e:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ a)) (cg (fun t => a ◇ t) (p8 a))).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ a)) (cg (fun t => a ◇ t) (cg (fun t => t ◇ a) (cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (p1b a))))).symm).trans (pn ((a ◇ a) ◇ a) a)).trans ((cg (fun t => t ◇ a) (cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (p1b a))).trans (p8 a)))
  have p1f:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p16 a))).symm).trans (((cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p1e (a ◇ a)))).symm).trans (p9 a a a (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a))))
  have p1g:=fun (a:G)=>by
    exact (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (p16 a)))).symm).trans ((((cg (fun t => t ◇ (a ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)) ◇ (a ◇ a)))) (p1e (a ◇ a))).symm).trans (p5 a a a (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)))).trans (cg (fun t => t ◇ (a ◇ a)) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))))
  have p1h:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) ((h a a a).symm)).symm).trans (p1g (a ◇ a))).trans (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))
  have p1i:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1d a))).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (p1d a)).symm).trans (p1g (a ◇ (a ◇ a)))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1d a)))
  have p1j:=fun (a:G)=>by
    exact ((((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))) (cg (fun t => t ◇ (a ◇ a)) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))))).trans (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p2 a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))))).trans (p1i a)).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)) ◇ t) (p1g (a ◇ a)))).symm).trans (pb a a a ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))
  have p1k:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ a) (p1b (a ◇ a))).symm).trans (p15 a)).symm
  have p1l:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (cg (fun t => a ◇ t) (p1d a))).trans (cg (fun t => (a ◇ a) ◇ t) (p1d a))).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (p1d a))).symm).trans (p1k (a ◇ (a ◇ a)))).trans (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a)))
  have p1m:=fun (a:G)=>by
    exact (((((cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ (a ◇ a)))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1g a)))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (p1g a)))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a)))).trans (cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ a)))) (p16 a))).symm).trans (((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ (a ◇ a)))) ◇ ((a ◇ a) ◇ (a ◇ (a ◇ a))))) (cg (fun t => t ◇ (a ◇ a)) (p1g a))).symm).trans (pt (a ◇ (a ◇ a)) (a ◇ a) a))
  have p1n:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ b) ◇ (a ◇ b))) (cg (fun t => t ◇ a) (p1b b))).symm).trans (py a b)
  have p1o:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ b) (p1b a)))).symm).trans (pz a b)
  have p1p:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p1b b))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have p1q:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1b a))).symm).trans ((h a b ((a ◇ a) ◇ a)).symm)
  have p1r:=fun (a:G)=>by
    exact ((((cg (fun t => a ◇ t) (p1j a)).trans (p17 a)).symm).trans (((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ a)) (p1q a a)).symm).trans (pq (a ◇ a) a))).symm
  have p1s:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (cg (fun t => t ◇ (a ◇ (((a ◇ a) ◇ a) ◇ a))) (p1b a))).trans (cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (cg (fun t => a ◇ t) (p1c a)))).trans (cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (p1b a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (cg (fun t => t ◇ (a ◇ (((a ◇ a) ◇ a) ◇ a))) (cg (fun t => a ◇ t) (p1c a)))).symm).trans (p13 a ((a ◇ a) ◇ a) b)).trans (p1c a))
  have p1t:=fun (a:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (p1d a))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => a ◇ t) (p1d a)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1d a))).symm).trans (p18 (a ◇ (a ◇ a)))).trans (p1d a))
  have p1u:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) (cg (fun t => (a ◇ a) ◇ t) (p1b a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) (cg (fun t => t ◇ (a ◇ ((a ◇ a) ◇ a))) (cg (fun t => a ◇ t) (p1b a)))).symm).trans (p13 a (a ◇ a) b)).trans (p1b a))
  have p1v:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a))) (p1k a))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a))) ◇ t) (p1f a))).trans (cg (fun t => t ◇ (a ◇ a)) (pp b a))).symm).trans (((cg (fun t => ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (ph a b))).symm).trans (p1p (((b ◇ a) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)) (a ◇ a)))).symm
  have p1w:=fun (a b:G)=>by
    exact (((((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p3 a))).trans (cg (fun t => a ◇ t) (p17 a))).trans (p17 a)).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ t) (p1v a b))).symm).trans (pb a a b ((a ◇ a) ◇ a)))).symm
  have p1x:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (p1h b))).trans (p3 b)).symm).trans (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ b) (p1w b a)))).symm).trans (pe b a b))).symm
  have p1y:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1r a))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (p18 a))).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) (p1c a))).symm).trans (p1x a (((a ◇ a) ◇ a) ◇ a)))
  have p1z:=fun (a:G)=>by
    exact ((((cg (fun t => (a ◇ a) ◇ t) (p0 a a)).trans (p1g a)).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ a) (p1l a))).symm).trans (p1y a))).symm
  have p20:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1k b)).symm).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (cg (fun t => t ◇ (b ◇ b)) (p1w b a))).symm).trans (p10 a b))
  have p21:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ t) (p1b a)).symm).trans (((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1c a))).symm).trans (p5 a ((a ◇ a) ◇ a) b a))
  have p22:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (pg a)))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (p1b a)))).symm).trans (((cg (fun t => ((a ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ b) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (p1f a)))).symm).trans (p11 a ((a ◇ a) ◇ a) b))
  have p23:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ (b ◇ c))) (p1x a b)).symm).trans ((h b ((a ◇ b) ◇ (b ◇ a)) c).symm)
  have p24:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ c) ◇ (c ◇ a)))) (p1x a c))).symm).trans ((h b c ((a ◇ c) ◇ (c ◇ a))).symm)
  have p25:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b))) (p0 a a)).symm).trans (((cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b))) (cg (fun t => t ◇ a) (p1l a))).symm).trans (p14 a b))
  have p26:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (p1l a)))).symm).trans (p4 a b)
  have p27:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ c) ◇ (c ◇ a))) ◇ t) (cg (fun t => (c ◇ b) ◇ t) (p1x a c))).symm).trans ((h ((a ◇ c) ◇ (c ◇ a)) b c).symm)
  have p28:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ (a ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b))) ◇ t) (p16 a)).trans (cg (fun t => t ◇ (a ◇ a)) (p25 a b))).symm).trans (((cg (fun t => ((a ◇ (a ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p1g a))).symm).trans (p27 b (a ◇ (a ◇ a)) (a ◇ a)))).symm
  have p29:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)) ◇ t) ((h b b a).symm)).symm).trans (p28 b ((a ◇ b) ◇ (b ◇ a)))
  have p2a:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (c ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (a ◇ b)) (p1b b)))).symm).trans (p5 a ((b ◇ b) ◇ b) b c)
  have p2b:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (cg (fun t => b ◇ t) (p1l a)))).symm).trans (p6 a b)
  have p2c:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ a)) (cg (fun t => b ◇ t) (p1l a))).symm).trans (pa a b)
  have p2d:=fun (a b c:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ (b ◇ a)) ◇ t) ((h a b c).symm)).symm).trans (p1w (b ◇ a) ((c ◇ b) ◇ (a ◇ c)))
  have p2e:=fun (a b c:G)=>by
    exact (p2d a b c).trans ((p2d a b a).symm)
  have p2f:=fun (a b c:G)=>by
    exact (((cg (fun t => a ◇ t) (cg (fun t => (c ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (a ◇ b)) (p1b b))))).symm).trans (pb a ((b ◇ b) ◇ b) b c)).trans (cg (fun t => t ◇ (a ◇ b)) (p1b b))
  have p2g:=fun (a b c:G)=>by
    exact (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ c)) (cg (fun t => c ◇ t) (p20 a b)))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p28 b c))).symm).trans ((((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => (c ◇ (((b ◇ b) ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (p1x a b))))).symm).trans (p2f ((a ◇ b) ◇ (b ◇ a)) b c)).trans (cg (fun t => b ◇ t) (p1x a b)))
  have p2h:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p21 b a)).symm).trans (p1w b (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))
  have p2i:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p2g a b a)).symm).trans (p1w (b ◇ (b ◇ b)) ((a ◇ b) ◇ (b ◇ a)))).trans ((cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))) (p1d b)).trans (cg (fun t => b ◇ t) (p1d b)))
  have p2j:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p23 a b (b ◇ (b ◇ b)))).symm).trans (((cg (fun t => t ◇ (b ◇ (((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ (b ◇ (b ◇ (b ◇ b)))))) (p2i a b)).symm).trans (p26 b ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a)))))).symm
  have p2k:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2g a b (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p3 b))).symm).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (p2j a b))).symm).trans (p1x (b ◇ (b ◇ b)) ((a ◇ b) ◇ (b ◇ a))))
  have p2l:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (p2k a b)).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => b ◇ t) (p2k a b))).symm).trans (p24 a b b))
  have p2m:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b))) (p1x a b)).symm).trans (((cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p2k a b))).symm).trans (p1o b ((a ◇ b) ◇ (b ◇ a))))
  have p2n:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p29 a b))).trans (cg (fun t => b ◇ t) (p1g b))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ ((((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)) ◇ b))) (p2m a b)).symm).trans (p1n (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ b)) b))).symm
  have p2o:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1x a b))).symm).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ b))) (p2k a b)).symm).trans (p1n ((a ◇ b) ◇ (b ◇ a)) b))
  have p2p:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ a)) ◇ t) (p4 b (a ◇ b)))).symm).trans (pb a b b (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))))
  have p2q:=fun (a b:G)=>by
    exact (((((((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p1d b))))))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1m b)))))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p16 b))))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => (b ◇ b) ◇ t) (p2j a b))))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (p1f b)))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p2g a b (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b))))))).symm).trans ((((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b))) ◇ (b ◇ (b ◇ b)))) (p2g a b a)))))).symm).trans (p2p ((a ◇ b) ◇ (b ◇ a)) (b ◇ (b ◇ b)))).trans ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))) (p1d b)).trans (cg (fun t => b ◇ t) (p2g a b (((a ◇ b) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ b)))))))
  have p2r:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ c) ◇ t) (cg (fun t => t ◇ (c ◇ (b ◇ a))) (p1w a b))).symm).trans ((h c (a ◇ b) (b ◇ a)).symm)
  have p2s:=fun (a b c d e:G)=>by
    exact ((cg (fun t => (e ◇ (((c ◇ b) ◇ (a ◇ c)) ◇ d)) ◇ t) (cg (fun t => ((a ◇ (d ◇ (b ◇ a))) ◇ e) ◇ t) (p5 a b c d))).symm).trans ((h (((c ◇ b) ◇ (a ◇ c)) ◇ d) e (a ◇ (d ◇ (b ◇ a)))).symm)
  have p2t:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ c))) (p1w a b)).symm).trans ((h (a ◇ b) (b ◇ a) c).symm)
  have p2u:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ a)) ◇ (b ◇ (a ◇ b))) ◇ t) (p2t b a b)).symm).trans (p2r b (b ◇ a) (b ◇ (a ◇ b)))
  have p2v:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p1b b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p1s b a))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p2h a b))).trans (p2o b b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p1s b a)))).symm).trans (p2u ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) b))).symm
  have p2w:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p21 b a))).trans (cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (p1x b b))).trans (p2v a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ b)) (p2v a b))).symm).trans (p1x b (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)))).symm
  have p2x:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (p1n b b)).trans (cg (fun t => t ◇ b) (p1s b a))).trans (p1z b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p2w a b))).symm).trans (p1n ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) b))).symm
  have p2y:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p2n b b))))).trans (cg (fun t => (b ◇ ((a ◇ (b ◇ (b ◇ (b ◇ b)))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p28 b (b ◇ b))))).trans (cg (fun t => (b ◇ ((a ◇ (b ◇ (b ◇ (b ◇ b)))) ◇ ((b ◇ b) ◇ a))) ◇ t) (p1w b (b ◇ b)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p2b b a))).trans (p1n b b)).symm).trans ((((cg (fun t => (b ◇ ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p2w a (b ◇ b)))).symm).trans (p22 b ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p2n b b))))).symm
  have p2z:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (b ◇ (b ◇ (b ◇ b))))) (p2c b a)).symm).trans ((((cg (fun t => t ◇ (a ◇ (b ◇ (b ◇ (b ◇ b))))) (cg (fun t => (a ◇ (b ◇ (b ◇ (b ◇ b)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p2y a b)))).symm).trans (p0 ((b ◇ b) ◇ a) (a ◇ (b ◇ (b ◇ (b ◇ b)))))).trans (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p2y a b)))
  have p30:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ b) ◇ c) ◇ t) (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (cg (fun t => c ◇ t) (p20 a b)))).symm).trans (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ (c ◇ (((b ◇ b) ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a)))))) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (p1x a b)))).symm).trans (p2a ((a ◇ b) ◇ (b ◇ a)) b c))
  have p31:=fun (a b:G)=>by
    exact (((((cg (fun t => (((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ (a ◇ a)))) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ (a ◇ a)))))) (cg (fun t => (a ◇ a) ◇ t) (p1t a)))).trans (cg (fun t => (((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ (a ◇ a)))) ◇ b) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => b ◇ t) (ps a a))))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (b ◇ (a ◇ (a ◇ (a ◇ a)))))) (cg (fun t => t ◇ b) (ps a a)))).trans (cg (fun t => ((a ◇ (a ◇ (a ◇ a))) ◇ b) ◇ t) (p2z b a))).symm).trans (((cg (fun t => (((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ (a ◇ a)))) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ (a ◇ a)))))) (cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a))) (p1m a)))).symm).trans (p30 (a ◇ a) (a ◇ (a ◇ (a ◇ a))) b))
  have p32:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ b) ◇ (a ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1j a)))).trans (cg (fun t => (((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p1d a))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (p2j a a)))).symm).trans (((cg (fun t => t ◇ ((((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ b) ◇ (a ◇ (a ◇ a)))) (cg (fun t => t ◇ b) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1d a))))).symm).trans (p31 (a ◇ (a ◇ a)) b))
  have p33:=fun (a b:G)=>by
    exact ((((((((cg (fun t => t ◇ (a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))))) (cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pg a)))).trans (cg (fun t => ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pg a))))).trans (cg (fun t => t ◇ (a ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))) (cg (fun t => t ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) (pg a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) ◇ t) (cg (fun t => a ◇ t) (pg a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) ◇ t) (p1b a))).trans (cg (fun t => t ◇ a) (p1u a b))).symm).trans (((cg (fun t => (((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))) (p1u a b))).symm).trans (p32 ((a ◇ a) ◇ a) ((b ◇ (a ◇ a)) ◇ (a ◇ b))))).symm
  have p34:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ b)))) (p2k a b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (p1l b)).symm).trans (p27 a b b))
  have p35:=fun (a b c:G)=>by
    exact ((((cg (fun t => c ◇ t) (cg (fun t => ((b ◇ c) ◇ (c ◇ b)) ◇ t) (p2n a c))).trans (cg (fun t => c ◇ t) (p34 b c))).trans (p2k b c)).symm).trans (((cg (fun t => t ◇ (((b ◇ c) ◇ (c ◇ b)) ◇ (((a ◇ c) ◇ (c ◇ a)) ◇ (c ◇ c)))) ((h c c a).symm)).symm).trans (p30 b c ((a ◇ c) ◇ (c ◇ a))))
  have p36:=fun (a b c d e:G)=>by
    exact (((p2s b b a c d).symm).trans ((((cg (fun t => t ◇ (((b ◇ (c ◇ (b ◇ b))) ◇ d) ◇ c)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (p35 a e b)))).symm).trans (p2s b b e c d)).trans (cg (fun t => t ◇ c) (p1w b e)))).symm
  have p37:=fun (a b c d:G)=>by
    exact ((p2e a b d).symm).trans (((cg (fun t => (((d ◇ b) ◇ (a ◇ d)) ◇ (b ◇ a)) ◇ t) ((h a b d).symm)).symm).trans (p35 c ((d ◇ b) ◇ (a ◇ d)) (b ◇ a)))
  have p38:=fun (a b c d:G)=>by
    exact ((p37 a b d c).symm).trans (p37 a b a c)
  have p39:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ c) ◇ (c ◇ b)) ◇ t) (p35 a c c)).symm).trans (p2q b c)
  have p3a:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1w a b)).symm).trans (p35 c (b ◇ a) (a ◇ b))).trans (p38 b a ((c ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ c)) c)
  have p3b:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ c) ◇ (c ◇ a))) (p1w b c)).symm).trans ((((cg (fun t => ((c ◇ b) ◇ (b ◇ c)) ◇ t) (p35 a b c)).symm).trans (p35 d (c ◇ b) (b ◇ c))).trans (p38 c b ((d ◇ (b ◇ c)) ◇ ((b ◇ c) ◇ d)) d))
  have p3c:=fun (a b c:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1w b (a ◇ a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ (b ◇ (a ◇ a)))) (p28 a b)).symm).trans (p35 c (b ◇ (a ◇ a)) ((a ◇ a) ◇ b))).trans (p38 b (a ◇ a) ((c ◇ ((a ◇ a) ◇ b)) ◇ (((a ◇ a) ◇ b) ◇ c)) c))).symm
  have p3d:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p35 a b b)).symm).trans (p3a b c a)
  have p3e:=fun (a b c:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (p38 a a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) (a ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p39 a a (a ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (p1n a a))).symm).trans ((((cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ b))) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (p3d a a a))).symm).trans (p3b b ((a ◇ a) ◇ (a ◇ a)) c a)).trans ((p3c (a ◇ a) c ((c ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ c)) ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ c) ◇ c))).trans (cg (fun t => t ◇ ((c ◇ c) ◇ (c ◇ c))) (p1n a a))))).symm
  have p3f:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p1f a))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (p3 a))).symm).trans ((p3e b ((a ◇ a) ◇ a) (a ◇ a)).symm)).trans (cg (fun t => b ◇ t) (p38 a a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) (a ◇ a))))).symm
  have p3g:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (p35 a b (b ◇ b))).symm).trans (p3f b c)
  have p3h:=fun (a b c:G)=>by
    exact (((p3f a ((c ◇ c) ◇ (c ◇ c))).symm).trans (p36 b c ((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) a a)).trans (p3g a a ((b ◇ c) ◇ (c ◇ b)))
  have p3i:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((d ◇ d) ◇ (d ◇ d)) ◇ t) (p2l a (b ◇ a))).symm).trans ((((cg (fun t => ((d ◇ d) ◇ (d ◇ d)) ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (p38 a b a (b ◇ a)))).symm).trans (p3h ((b ◇ a) ◇ (b ◇ a)) c d)).trans ((cg (fun t => ((c ◇ d) ◇ (d ◇ c)) ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (p38 a b (((b ◇ a) ◇ (b ◇ a)) ◇ ((b ◇ a) ◇ (b ◇ a))) (b ◇ a)))).trans (cg (fun t => ((c ◇ d) ◇ (d ◇ c)) ◇ t) (p2l a (b ◇ a)))))
  have p3j:=fun (a b c d:G)=>by
    exact ((p3i a b c d).symm).trans (p3i a b a d)
  have p3k:=fun (a b c d:G)=>by
    exact (((cg (fun t => ((b ◇ c) ◇ (c ◇ b)) ◇ t) (p1x d a)).symm).trans (p3j a ((d ◇ a) ◇ (a ◇ d)) b c)).trans (cg (fun t => ((a ◇ c) ◇ (c ◇ a)) ◇ t) (p1x d a))
  have p3l:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ a))) (p1b b))).symm).trans (pl a ((b ◇ b) ◇ b) b)
  have p3m:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (b ◇ a))))) (ps a b))).symm).trans (pc a b (b ◇ (a ◇ (b ◇ a))))
  have p3n:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (ps a b))).trans (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (p3l a b))).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3l a b)))).symm).trans (p0 (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))).trans ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3l a b)).trans (ps a b)))
  have p3o:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3l a b))).trans (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (ps a b))).trans (p3n a b)).symm).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p3n a b))).symm).trans (p1x (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))))).symm
  have p3p:=fun (a b:G)=>by
    exact (((((((((((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3o a b)))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))))) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3o a b)))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (ps a b)))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3o a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (ps a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (p3o a b)))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3o a b)))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (ps a b))).trans (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (ps a b))).trans (ps a b)).symm).trans (((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))))))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3o a b))).symm).trans (p3m (b ◇ (a ◇ (b ◇ a))) ((b ◇ b) ◇ b)))
  have p3q:=fun (a b:G)=>by
    exact ((p1z b).symm).trans (((cg (fun t => t ◇ b) (p3p a b)).symm).trans (p0 a b))
  have p3r:=fun (a b c:G)=>by
    exact (((p3q a c).symm).trans (p3q b c)).symm
  have p3s:=fun (a b:G)=>by
    exact ((p3q a (b ◇ b)).symm).trans ((h b b b).symm)
  have p3t:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ c) ◇ t) (p3r a c b)).symm).trans ((p3q (b ◇ c) c).symm)
  have p3u:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ b))) (p3q a b)).symm).trans (p1d b)
  have p3v:=fun (a b c:G)=>by
    exact (((cg (fun t => (a ◇ b) ◇ t) (p33 a b)).symm).trans (p3r c (a ◇ b) (b ◇ (a ◇ a)))).symm
  have p3w:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ (c ◇ a)) ◇ t) (p1n b b)).symm).trans (((cg (fun t => (a ◇ (c ◇ a)) ◇ t) (p3t a c (b ◇ b))).symm).trans (p3v b c (a ◇ (c ◇ a))))
  have p3x:=fun (a b c:G)=>by
    exact ((cg (fun t => a ◇ t) (p3k a b b (((b ◇ b) ◇ (b ◇ b)) ◇ a))).symm).trans ((((p3q a ((b ◇ b) ◇ (b ◇ b))).symm).trans (p36 c b (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))) a a)).trans (((cg (fun t => ((c ◇ b) ◇ (b ◇ c)) ◇ t) (p38 b b (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))) (b ◇ b))).trans (p3g b b ((c ◇ b) ◇ (b ◇ c)))).trans (p2g c b (((c ◇ b) ◇ (b ◇ c)) ◇ (b ◇ (b ◇ b))))))
  have p3y:=fun (a b:G)=>by
    exact (((((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3w a b b)))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p20 b b)))).trans (p3s b b)).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ (b ◇ a)) ◇ b)) (p3p a b)))).symm).trans (p3x b (a ◇ (b ◇ a)) a))).symm
  have p3z:=fun (a b:G)=>by
    exact ((((((cg (fun t => ((b ◇ a) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p2x a b))).trans (cg (fun t => t ◇ ((b ◇ a) ◇ (b ◇ (b ◇ b)))) (p3t b b a))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p3t b b a))).trans (p3u a a)).symm).trans (((cg (fun t => t ◇ ((b ◇ a) ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => (b ◇ a) ◇ t) (p2x a b))).symm).trans (p3y (b ◇ a) (a ◇ ((b ◇ b) ◇ b))))).symm
  exact (calc
    (x ◇ x)=(x ◇ x):=rfl
    _=((x ◇ ((y ◇ y) ◇ y)) ◇ x):=(cg (fun t => t ◇ x) (p3z x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19023_to_50327 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19023_to_50327
