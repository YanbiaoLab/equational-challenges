-- Equation61441 → Equation62284
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (y ◇ (z ◇ x)) ◇ z
-- Conclusion: (x ◇ y) ◇ z = ((y ◇ x) ◇ x) ◇ z
-- Original submission SHA-256: a1355ad2c97fa974c3a2485ee3d0b9e174373ae12c319b6e39bb4f790c718608
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ (z ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((y ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ d) ((h a b (d ◇ c)).symm)).symm).trans ((h c (b ◇ ((d ◇ c) ◇ a)) d).symm)).symm
  have p1:=fun (a b c:G)=>by
    exact (((p0 a c b c).symm).trans ((h ((c ◇ b) ◇ a) b c).symm)).symm
  have p2:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) ((h a (c ◇ b) b).symm)).symm).trans (p1 (b ◇ a) b c)).symm
  have p3:=fun (a b c:G)=>by
    exact (((p2 a b c).symm).trans ((h b ((b ◇ a) ◇ c) c).symm)).symm
  have p4:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (cg (fun t => b ◇ t) ((h a b c).symm))).symm).trans (p3 (c ◇ a) b c)).symm
  have p5:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) ((h b (b ◇ a) b).symm)).symm).trans (p4 a b b)).symm
  have p6:=fun (a b:G)=>by
    exact (((p3 a a b).symm).trans (((p4 a a b).symm).trans (p1 (b ◇ a) a b))).symm
  have p7:=fun (a b:G)=>by
    exact (((p6 a b).symm).trans ((h a ((b ◇ a) ◇ b) b).symm)).symm
  have p8:=fun (a b c d e:G)=>by
    exact ((cg (fun t => t ◇ e) (cg (fun t => d ◇ t) (cg (fun t => e ◇ t) ((h a b c).symm)))).symm).trans ((h ((b ◇ (c ◇ a)) ◇ c) d e).symm)
  have p9:=fun (a b c d e:G)=>by
    exact ((p8 a b c d e).symm).trans ((h ((a ◇ b) ◇ c) d e).symm)
  have pa:=fun (a b c d e f g i j k:G)=>by
    exact (p8 f g i j k).trans (p9 f g i j k)
  have pb:=fun (a b c:G)=>by
    exact (((p1 a (c ◇ b) c).symm).trans ((h b ((c ◇ (c ◇ b)) ◇ a) c).symm)).symm
  have pc:=fun (a b:G)=>by
    exact (((p3 a b a).symm).trans (((cg (fun t => t ◇ a) (cg (fun t => b ◇ t) ((h b a a).symm))).symm).trans (pb a b a))).symm
  have pd:=fun (a b:G)=>by
    exact ((pc b a).symm).trans ((h (b ◇ a) (b ◇ b) b).symm)
  have pe:=fun (a b c d e:G)=>by
    exact (((cg (fun t => t ◇ e) (cg (fun t => t ◇ (e ◇ d)) ((h a b c).symm))).symm).trans ((h d ((b ◇ (c ◇ a)) ◇ c) e).symm)).symm
  have pf:=fun (a b c d e:G)=>by
    exact (((cg (fun t => t ◇ e) (cg (fun t => d ◇ t) ((h a b c).symm))).symm).trans (pe a b c d e)).symm
  have pg:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) (p7 a b)).symm).trans (((p3 a b (b ◇ a)).symm).trans ((h (b ◇ a) b (b ◇ a)).symm))
  have ph:=fun (a b:G)=>by
    exact (((pd (b ◇ a) b).symm).trans ((h a (b ◇ (b ◇ (b ◇ a))) b).symm)).symm
  have pi:=fun (a b:G)=>by
    exact (((ph a b).symm).trans ((h (b ◇ (b ◇ a)) a b).symm)).trans (pd a b)
  have pj:=fun (a b:G)=>by
    exact (((pi a b).symm).trans ((h b (b ◇ (b ◇ a)) b).symm)).symm
  have pk:=fun (a b:G)=>by
    exact ((pj a b).symm).trans ((h (b ◇ a) b b).symm)
  have pl:=fun (a b:G)=>by
    exact (((pk a b).symm).trans ((h b (b ◇ a) b).symm)).symm
  have pm:=fun (a b:G)=>by
    exact ((pl a b).symm).trans ((h a b b).symm)
  have pn:=fun (a b c d:G)=>by
    exact (pl a b).trans (pm a b)
  have po:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) ((h a b b).symm)).symm).trans (pm (b ◇ a) b)).trans (pm a b)
  have pp:=fun (a b c d:G)=>by
    exact ((pd a b).trans (pk a b)).trans (pm a b)
  have pq:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (po b a)).symm).trans (p1 a a b)).symm
  have pr:=fun (a b:G)=>by
    exact (((pq a b).symm).trans ((h a (a ◇ b) b).symm)).symm
  have ps:=fun (a b c d e f:G)=>by
    exact ((cg (fun t => t ◇ b) (pr b a)).symm).trans (pp a b a a)
  have pt:=fun (a b c:G)=>by
    exact (((po (a ◇ b) c).symm).trans (((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) ((h a b c).symm))).symm).trans (po (b ◇ (c ◇ a)) c))).symm
  have pu:=fun (a b:G)=>by
    exact (((((pt b (a ◇ b) b).trans (pm (a ◇ b) b)).trans (po a b)).symm).trans ((((cg (fun t => t ◇ b) (p1 a b b)).symm).trans (po ((b ◇ b) ◇ a) b)).trans (p1 a b b))).symm
  have pv:=fun (a b:G)=>by
    exact (((pu a b).symm).trans ((h b (a ◇ b) b).symm)).symm
  have pw:=fun (a b c d:G)=>by
    exact (p7 c d).trans (cg (fun t => t ◇ d) (pv d c))
  have px:=fun (a b c d e:G)=>by
    exact ((((pf a b ((e ◇ d) ◇ c) d e).trans (p0 c (a ◇ b) d e)).symm).trans (((cg (fun t => t ◇ e) (p0 a b c (e ◇ d))).symm).trans ((h d (c ◇ (b ◇ (((e ◇ d) ◇ c) ◇ a))) e).symm))).symm
  have py:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ b) (pv b a))).symm).trans (pg a b)
  have pz:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (pr b a))).symm).trans (pb a a b)
  have p10:=fun (a b c d e f g i j k:G)=>by
    exact (pe f g i j k).trans (pf f g i j k)
  have p11:=fun (a b c:G)=>by
    exact ((pq (a ◇ b) c).symm).trans (pf a b c (a ◇ b) c)
  have p12:=fun (a b:G)=>by
    exact ((pr (b ◇ a) b).symm).trans (((p11 b a b).symm).trans ((h a (b ◇ (b ◇ a)) b).symm))
  have p13:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => (b ◇ a) ◇ t) ((h a b b).symm))).symm).trans (pw a a (b ◇ a) b)).trans (p12 a b)
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (pr a b))).symm).trans (p3 (a ◇ b) a b)
  have p15:=fun (a b:G)=>by
    exact ((((pf b a b a b).trans (pw ((a ◇ ((b ◇ a) ◇ b)) ◇ b) ((a ◇ ((b ◇ a) ◇ b)) ◇ b) a b)).symm).trans ((((cg (fun t => t ◇ b) (py a b a a)).symm).trans ((h a (((b ◇ a) ◇ a) ◇ b) b).symm)).trans (p14 a b))).symm
  have p16:=fun (a b c d:G)=>by
    exact (((px a b d c d).symm).trans ((h (b ◇ (((d ◇ c) ◇ d) ◇ a)) c d).symm)).symm
  have p17:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ a) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (pm c a)))).symm).trans (p16 a b c a)
  have p18:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (pv ((b ◇ a) ◇ b) a)).symm).trans (p16 a a a b)
  have p19:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) ((h a (b ◇ (b ◇ a)) b).symm)).symm).trans (ps b (b ◇ a) a a a a)
  have p1a:=fun (a b:G)=>by
    exact (((py a b ((((b ◇ a) ◇ a) ◇ b) ◇ (b ◇ a)) ((((b ◇ a) ◇ a) ◇ b) ◇ (b ◇ a))).symm).trans (((cg (fun t => t ◇ (b ◇ a)) ((h (b ◇ a) a b).symm)).symm).trans (p19 a b))).symm
  have p1b:=fun (a b c d:G)=>by
    exact ((((pf d c d c d).trans (pw ((c ◇ ((d ◇ c) ◇ d)) ◇ d) ((c ◇ ((d ◇ c) ◇ d)) ◇ d) c d)).symm).trans (((cg (fun t => t ◇ d) (p1a c d)).symm).trans (p12 c d))).symm
  have p1c:=fun (a b c d e f:G)=>by
    exact (p13 a b).trans (p1b ((a ◇ (b ◇ (b ◇ a))) ◇ b) ((a ◇ (b ◇ (b ◇ a))) ◇ b) a b)
  have p1d:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (po c a))))).symm).trans (px a b a a c)
  have p1e:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (po a (c ◇ b))).symm).trans ((h b ((a ◇ (c ◇ b)) ◇ (c ◇ b)) c).symm)).symm
  have p1f:=fun (a b:G)=>by
    exact ((p1c a b (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b)).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => (b ◇ a) ◇ t) (pm a b))).symm).trans (p3 b (b ◇ a) b)).trans ((((((cg (fun t => t ◇ b) (pr b (b ◇ a))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ a)) (pm a b)))).trans (pf a b b a b)).trans (p3 b a b)).trans (cg (fun t => t ◇ b) (pr b a))).trans (ps a b ((((a ◇ b) ◇ b) ◇ a) ◇ b) ((((a ◇ b) ◇ b) ◇ a) ◇ b) ((((a ◇ b) ◇ b) ◇ a) ◇ b) ((((a ◇ b) ◇ b) ◇ a) ◇ b))))
  have p1g:=fun (a b c d e f g i:G)=>by
    exact (p1c a b a a a a).trans (p1f a b)
  have p1h:=fun (a b c d:G)=>by
    exact (p15 c d).trans (p1f c d)
  have p1i:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ b)) (po a b)).symm).trans (p1f b (a ◇ b))).symm
  have p1j:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ d) (cg (fun t => c ◇ t) (p1f d c))).symm).trans (pz c d)).symm
  have p1k:=fun (a b:G)=>by
    exact ((p1j a a a b).symm).trans ((h (b ◇ a) (a ◇ b) b).symm)
  have p1l:=fun (a b:G)=>by
    exact (((p1h ((((b ◇ a) ◇ (a ◇ b)) ◇ b) ◇ a) ((((b ◇ a) ◇ (a ◇ b)) ◇ b) ◇ a) b a).symm).trans (((cg (fun t => t ◇ a) (p1k a b)).symm).trans (p17 a a b))).symm
  have p1m:=fun (a b:G)=>by
    exact (((p1l b a).symm).trans ((h a (b ◇ (b ◇ b)) b).symm)).symm
  have p1n:=fun (a b:G)=>by
    exact (((p1m a b).symm).trans ((h (b ◇ b) a b).symm)).symm
  have p1o:=fun (a b:G)=>by
    exact (((pm a b).symm).trans (((p1n (b ◇ a) b).symm).trans ((h a (b ◇ b) b).symm))).symm
  have p1p:=fun (a b:G)=>by
    exact ((p1o b a).symm).trans ((h a b a).symm)
  have p1q:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ d) (p1p c d)).symm).trans (p1f c d)
  have p1r:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) ((h a b c).symm)).symm).trans (p1p c (b ◇ (c ◇ a)))).symm
  have p1s:=fun (a b c d:G)=>by
    exact (p1l a b).trans (p1p a b)
  have p1t:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ a) (p1q a a a b)).symm).trans (p1 a b a)).trans (((p1n (a ◇ b) a).trans (pm b a)).trans (p1p a b))
  have p1u:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p1p a b))).symm).trans (p1k a b)
  have p1v:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (p1p a c)))).symm).trans (p0 a b a c)
  have p1w:=fun (a b c d e f:G)=>by
    exact ((((((cg (fun t => t ◇ f) (cg (fun t => t ◇ e) (p1p e f))).trans (cg (fun t => t ◇ f) (pm f e))).trans (cg (fun t => t ◇ f) (p1p e f))).trans (p1q (((e ◇ f) ◇ e) ◇ f) (((e ◇ f) ◇ e) ◇ f) e f)).symm).trans (((cg (fun t => t ◇ f) (cg (fun t => t ◇ e) (p1q (((f ◇ e) ◇ f) ◇ e) (((f ◇ e) ◇ f) ◇ e) f e))).symm).trans (p18 e f))).symm
  have p1x:=fun (a b:G)=>by
    exact (((p1w a a a a a b).symm).trans ((h a (b ◇ (a ◇ a)) b).symm)).symm
  have p1y:=fun (a b:G)=>by
    exact (((p1x a b).symm).trans ((h (a ◇ a) a b).symm)).symm
  have p1z:=fun (a b c:G)=>by
    exact (((pf c b a b c).symm).trans (((cg (fun t => t ◇ c) (p1p (c ◇ b) a)).symm).trans ((h b (a ◇ (c ◇ b)) c).symm))).symm
  have p20:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ d) (cg (fun t => t ◇ c) (p1s b a a a))).symm).trans (p9 a (b ◇ (b ◇ b)) b c d)).trans (cg (fun t => t ◇ d) (cg (fun t => t ◇ c) (p1m a b)))
  have p21:=fun (a b c d:G)=>by
    exact (((pf a b b c d).symm).trans (((p20 a b (d ◇ c) d).symm).trans ((h c ((b ◇ a) ◇ b) d).symm))).symm
  have p22:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (p1p (c ◇ b) a)).trans (pf c b a b c)).symm).trans (((cg (fun t => t ◇ c) (p1y a (c ◇ b))).symm).trans ((h b ((a ◇ a) ◇ a) c).symm))
  have p23:=fun (a b c d e f:G)=>by
    exact (p1z a b c).trans (p22 a b c)
  have p24:=fun (a b:G)=>by
    exact (((p23 b a b a a a).symm).trans ((h (b ◇ a) a b).symm)).trans ((cg (fun t => t ◇ b) (p1p a b)).trans (p1q (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) a b))
  have p25:=fun (a b c:G)=>by
    exact ((p21 a b c (a ◇ b)).symm).trans (((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => c ◇ t) (p1p b a))).symm).trans ((h b c (a ◇ b)).symm))
  have p26:=fun (a b:G)=>by
    exact (((p1u a b ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p1p a b))).symm).trans (p22 a a b))).symm
  have p27:=fun (a b c:G)=>by
    exact ((p21 a b c (b ◇ a)).symm).trans ((h b c (b ◇ a)).symm)
  have p28:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (p27 b c a)).symm).trans ((h b (a ◇ ((b ◇ c) ◇ c)) c).symm)).symm
  have p29:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => t ◇ a) (cg (fun t => b ◇ t) (p1p a c)))).symm).trans (((cg (fun t => t ◇ c) (cg (fun t => t ◇ a) (cg (fun t => b ◇ t) (p1q a a c a)))).symm).trans (p16 a b a c))
  have p2a:=fun (a b c d:G)=>by
    exact ((((cg (fun t => t ◇ d) (p0 a b (d ◇ c) c)).symm).trans (p1 (b ◇ ((c ◇ (d ◇ c)) ◇ a)) c d)).trans (pf b ((c ◇ (d ◇ c)) ◇ a) d c d)).symm
  have p2b:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ a) (cg (fun t => c ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (p1p a c))))).symm).trans (((cg (fun t => t ◇ a) (cg (fun t => c ◇ t) (cg (fun t => a ◇ t) (cg (fun t => b ◇ t) (pm c a))))).symm).trans (px a b a c a))
  have p2c:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (p1p a c)))).symm).trans ((((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (p1y c a)))).symm).trans (p16 a b c c)).trans ((p1o (c ◇ (a ◇ b)) c).trans (pm (a ◇ b) c)))
  have p2d:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p1u a b a a)).symm).trans (p2c a a b)
  have p2e:=fun (a b:G)=>by
    exact (((p1g a b (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b) (((b ◇ a) ◇ ((a ◇ b) ◇ b)) ◇ b)).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => (b ◇ a) ◇ t) (p1f a b))).symm).trans (p3 a (b ◇ a) b))).symm
  have p2f:=fun (a b:G)=>by
    exact (((p2e a b).symm).trans ((h a (a ◇ (b ◇ (b ◇ a))) b).symm)).symm
  have p2g:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (cg (fun t => t ◇ (b ◇ a)) (p1p a b)))).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p1i b a))).symm).trans (p1e a a b)).trans ((((cg (fun t => t ◇ b) (p1p (b ◇ a) a)).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ a)) (p1p a b)))).trans (pf a b a a b)).trans (p1u a b ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b))))
  have p2h:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (p1p a b))).symm).trans (((cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (p1o b a))).symm).trans (p22 a (a ◇ a) b))
  have p2i:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ a) (cg (fun t => c ◇ t) (cg (fun t => t ◇ a) (cg (fun t => b ◇ t) ((h c c a).symm))))).symm).trans (p2a a b c a)
  have p2j:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ a) (cg (fun t => b ◇ t) (pv (b ◇ b) a))).symm).trans (p2i a a b)).symm
  have p2k:=fun (a b:G)=>by
    exact ((((((p1 (a ◇ a) b a).trans (pf a a a b a)).trans (p24 b a)).trans (p1p a b)).symm).trans (((cg (fun t => t ◇ a) ((h (a ◇ b) (a ◇ a) b).symm)).symm).trans (p2j a b))).symm
  have p2l:=fun (a b c d:G)=>by
    exact (p2j c d).trans (p2k c d)
  have p2m:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (p2l a a b a)).symm).trans (p9 (b ◇ a) (b ◇ b) a b c)).symm
  have p2n:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (pf b b b a b)).trans (cg (fun t => t ◇ c) (p24 a b))).symm).trans (((cg (fun t => t ◇ c) (p1 (b ◇ b) a b)).symm).trans (p2m a b c))).symm
  have p2o:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ a) (cg (fun t => t ◇ b) (p1p a b))).trans (cg (fun t => t ◇ a) (p1q (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) a b))).trans (p1t a b)).symm).trans ((((cg (fun t => t ◇ a) (p2n b a b)).symm).trans (p1 a b a)).trans (p1n (a ◇ b) a))).symm
  have p2p:=fun (a b c d e f:G)=>by
    exact (((cg (fun t => t ◇ f) (p10 a a a a a a b c d (f ◇ e))).symm).trans ((h e (d ◇ ((b ◇ (c ◇ a)) ◇ c)) f).symm)).symm
  have p2q:=fun (a b c d e f:G)=>by
    exact (((cg (fun t => t ◇ f) (cg (fun t => e ◇ t) (cg (fun t => d ◇ t) ((h a b c).symm)))).symm).trans (p2p a b c d e f)).symm
  have p2r:=fun (a b c d e:G)=>by
    exact ((cg (fun t => t ◇ e) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (cg (fun t => d ◇ t) (p1p c e))))).symm).trans (p1d c d e)
  have p2s:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ b)) (ps a b a a a a)).symm).trans (p1 a b (a ◇ b))).trans (p25 a b (a ◇ (a ◇ b)))).symm
  have p2t:=fun (a b c d:G)=>by
    exact ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ a)) (p1p a b))).trans (pf a b a a b)).trans (p1u a b ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b))).symm).trans (((cg (fun t => t ◇ b) (p2s b a)).symm).trans (p2e a b))
  have p2u:=fun (a b c d e f:G)=>by
    exact (((po c d).symm).trans (((cg (fun t => t ◇ d) (p2t c d (((d ◇ c) ◇ (c ◇ d)) ◇ d) (((d ◇ c) ◇ (c ◇ d)) ◇ d))).symm).trans (p2d c d))).symm
  have p2v:=fun (a b c d e f g i:G)=>by
    exact (p1u c d c c).trans (p2t c d (((d ◇ c) ◇ (c ◇ d)) ◇ d) (((d ◇ c) ◇ (c ◇ d)) ◇ d))
  have p2w:=fun (a b c d e f:G)=>by
    exact (p2g c d).trans (p2t c d (((d ◇ c) ◇ (c ◇ d)) ◇ d) (((d ◇ c) ◇ (c ◇ d)) ◇ d))
  have p2x:=fun (a b c d e f:G)=>by
    exact (p26 c d).trans (p2t c d (((d ◇ c) ◇ (c ◇ d)) ◇ d) (((d ◇ c) ◇ (c ◇ d)) ◇ d))
  have p2y:=fun (a b:G)=>by
    exact ((((p2w a a a b a a).symm).trans (p23 ((a ◇ b) ◇ a) a b a a a)).trans (((p1v a (((a ◇ b) ◇ a) ◇ ((a ◇ b) ◇ a)) b).trans (p2q (a ◇ b) a ((a ◇ b) ◇ a) a a b)).trans (p2r ((a ◇ (a ◇ (((a ◇ b) ◇ a) ◇ ((a ◇ b) ◇ a)))) ◇ b) ((a ◇ (a ◇ (((a ◇ b) ◇ a) ◇ ((a ◇ b) ◇ a)))) ◇ b) a ((a ◇ b) ◇ a) b))).symm
  have p2z:=fun (a b:G)=>by
    exact ((((p2y a b).symm).trans ((h a (a ◇ (a ◇ ((a ◇ b) ◇ a))) b).symm)).trans (p2r ((a ◇ (a ◇ (a ◇ ((a ◇ b) ◇ a)))) ◇ b) ((a ◇ (a ◇ (a ◇ ((a ◇ b) ◇ a)))) ◇ b) a a b)).symm
  have p30:=fun (a:G)=>by
    exact ((p1p (a ◇ a) a).symm).trans (((p2x a a a (a ◇ a) a a).symm).trans ((h a a (a ◇ a)).symm))
  have p31:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (p1p (a ◇ a) a))).trans (cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (p30 a)))).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => (a ◇ a) ◇ t) (p2u a a a (a ◇ a) a a))).symm).trans (p2x a a (a ◇ a) b a a)).trans (p2u (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b) a b (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b)))
  have p32:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ b) (p1p (b ◇ (a ◇ a)) a)).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p1o b a)))).trans (cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p1p a b)))).trans (pf a b a (a ◇ a) b)).trans (p2h a b)).symm).trans ((((cg (fun t => t ◇ b) (p31 a (b ◇ (a ◇ a)))).symm).trans (p2z (a ◇ a) b)).trans (p2u (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b) a b (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b)))
  have p33:=fun (a b c d:G)=>by
    exact (p2h a b).trans (p32 a b)
  have p34:=fun (a b c:G)=>by
    exact ((((pt b (c ◇ (c ◇ a)) c).trans (pt (c ◇ a) b c)).symm).trans ((((cg (fun t => t ◇ c) (p2b c a b)).symm).trans (pt (a ◇ ((c ◇ b) ◇ c)) b c)).trans (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p21 b c a b))))).symm
  have p35:=fun (a b c:G)=>by
    exact (((p1r (((c ◇ c) ◇ b) ◇ a) b c).symm).trans (px a c b c c)).trans (p1o (b ◇ (a ◇ c)) c)
  have p36:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) ((h a ((c ◇ c) ◇ b) b).symm))).symm).trans (p35 (b ◇ a) b c)).trans (cg (fun t => t ◇ c) (p3 a b c))
  have p37:=fun (a b c:G)=>by
    exact (((p17 c a (c ◇ b)).symm).trans ((h b (a ◇ (((c ◇ b) ◇ c) ◇ c)) c).symm)).trans (((cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p2n b c c)))).trans (cg (fun t => t ◇ c) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (po b c))))).trans (p28 a b c))
  have p38:=fun (a b c:G)=>by
    exact (((p37 a b c).symm).trans ((h (c ◇ b) (c ◇ (c ◇ a)) c).symm)).symm
  have p39:=fun (a b:G)=>by
    exact ((p25 a b (b ◇ b)).symm).trans ((((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (pv a b))).symm).trans (p33 b (a ◇ b) a a)).trans (p1p (a ◇ b) b))
  have p3a:=fun (a b c:G)=>by
    exact ((p1p ((a ◇ b) ◇ b) c).symm).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ b)) (cg (fun t => c ◇ t) (po a b))).symm).trans ((h b c ((a ◇ b) ◇ b)).symm))
  have p3b:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ b) ◇ b)) (po a b)).symm).trans (p3a a b b)
  have p3c:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (p3a a b c)).symm).trans (p1q a a ((a ◇ b) ◇ b) c)
  have p3d:=fun (a b:G)=>by
    exact (((p25 a b (b ◇ b)).trans (p39 a b)).symm).trans ((((cg (fun t => t ◇ (a ◇ b)) (p3b a b)).symm).trans ((h b ((a ◇ b) ◇ b) (a ◇ b)).symm)).trans (p25 a b b))
  have p3e:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ b) (p3d b a)).symm).trans ((h a ((b ◇ a) ◇ a) b).symm)).trans ((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p1p a b))).trans (p2v ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b) a b ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b) ((a ◇ ((a ◇ b) ◇ a)) ◇ b)))
  have p3f:=fun (a b:G)=>by
    exact (((p3e a b).symm).trans ((h a (a ◇ a) b).symm)).symm
  have p3g:=fun (a b c d:G)=>by
    exact (((p2b d (a ◇ b) c).symm).trans (pa a a a a a a b ((d ◇ c) ◇ d) c d)).trans (cg (fun t => t ◇ d) (p21 c d (a ◇ b) c))
  have p3h:=fun (a b c d:G)=>by
    exact ((p3g a b c d).symm).trans ((h c (d ◇ (d ◇ (a ◇ b))) d).symm)
  have p3i:=fun (a b c d e f g i:G)=>by
    exact (p3g a b c d).trans (p3h a b c d)
  have p3j:=fun (a b c d:G)=>by
    exact (((p38 c (a ◇ b) d).symm).trans ((((p16 a b (d ◇ c) d).symm).trans ((h c (b ◇ (((d ◇ (d ◇ c)) ◇ d) ◇ a)) d).symm)).trans (cg (fun t => t ◇ d) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (cg (fun t => t ◇ a) (pn c d ((d ◇ (d ◇ c)) ◇ d) ((d ◇ (d ◇ c)) ◇ d)))))))).symm
  have p3k:=fun (a b c:G)=>by
    exact (((p3j a c b c).symm).trans ((h (((b ◇ c) ◇ c) ◇ a) b c).symm)).symm
  have p3l:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) ((h a ((b ◇ c) ◇ c) b).symm)).symm).trans (p3k (b ◇ a) b c)).trans (((pa (((c ◇ b) ◇ (c ◇ ((b ◇ a) ◇ c))) ◇ c) (((c ◇ b) ◇ (c ◇ ((b ◇ a) ◇ c))) ◇ c) (((c ◇ b) ◇ (c ◇ ((b ◇ a) ◇ c))) ◇ c) (((c ◇ b) ◇ (c ◇ ((b ◇ a) ◇ c))) ◇ c) (((c ◇ b) ◇ (c ◇ ((b ◇ a) ◇ c))) ◇ c) b a c (c ◇ b) c).trans (pf b a c b c)).trans (p3 a b c))
  have p3m:=fun (a b c d e f:G)=>by
    exact ((cg (fun t => t ◇ f) (p3l d e f)).symm).trans (p34 d e f)
  have p3n:=fun (a b c d e f g:G)=>by
    exact (((p3l (d ◇ e) f g).symm).trans (p3h d e f g)).symm
  have p3o:=fun (a b c d:G)=>by
    exact ((p3n a a a a b c d).symm).trans ((h (d ◇ (a ◇ b)) c d).symm)
  have p3p:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ b) (p1p a b)).trans (p1q (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) a b)).symm).trans (((cg (fun t => t ◇ b) (p2t b a a a)).symm).trans (p3o a b a b))).symm
  have p3q:=fun (a b c d e f g i j:G)=>by
    exact (p36 a b c).trans (p3m ((((a ◇ (c ◇ b)) ◇ b) ◇ c) ◇ c) ((((a ◇ (c ◇ b)) ◇ b) ◇ c) ◇ c) ((((a ◇ (c ◇ b)) ◇ b) ◇ c) ◇ c) a b c)
  have p3r:=fun (a b c d e f g i j k l:G)=>by
    exact ((p3i d e f g d d d d).trans (p3n ((f ◇ (g ◇ (g ◇ (d ◇ e)))) ◇ g) ((f ◇ (g ◇ (g ◇ (d ◇ e)))) ◇ g) ((f ◇ (g ◇ (g ◇ (d ◇ e)))) ◇ g) d e f g)).trans (p3o d e f g)
  have p3s:=fun (a b c d:G)=>by
    exact (((p3o a b (d ◇ c) d).symm).trans ((h c ((a ◇ b) ◇ (d ◇ (d ◇ c))) d).symm)).symm
  have p3t:=fun (a b c:G)=>by
    exact ((p3s a b (a ◇ b) c).symm).trans (p2f (a ◇ b) c)
  have p3u:=fun (a b c:G)=>by
    exact (((p3t a b c).symm).trans ((h (a ◇ b) (c ◇ (a ◇ b)) c).symm)).symm
  have p3v:=fun (a b c:G)=>by
    exact (((p3u a b c).symm).trans ((h (a ◇ b) (a ◇ b) c).symm)).symm
  have p3w:=fun (a b:G)=>by
    exact ((((p2n a b b).trans (po a b)).symm).trans (((p3v b a b).symm).trans ((h a (b ◇ a) b).symm))).symm
  have p3x:=fun (a b:G)=>by
    exact ((p3w a b).symm).trans ((h a a b).symm)
  have p3y:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ b) (p3x a b)).symm).trans ((po a b).trans (p3x a b))
  have p3z:=fun (a b c d:G)=>by
    exact (p1n a b).trans (p3x a b)
  have p40:=fun (a b c d e f:G)=>by
    exact (p1q c c c d).trans (p3x c d)
  have p41:=fun (a b c d:G)=>by
    exact (p1y a b).trans (p3x a b)
  have p42:=fun (a b:G)=>by
    exact ((p3x b a).symm).trans (p1p a b)
  have p43:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ a) (p3x a b)).symm).trans (p1t a b)
  have p44:=fun (a b c d e:G)=>by
    exact (p2n a b c).trans (cg (fun t => t ◇ c) (p3x a b))
  have p45:=fun (a b c d e:G)=>by
    exact ((p42 c (a ◇ b)).symm).trans (p3v a b c)
  have p46:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (p3x a b)).symm).trans (p3d a b)
  have p47:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ a)) (p3x a b)).symm).trans (((cg (fun t => t ◇ (b ◇ a)) ((h a b b).symm)).symm).trans (p40 a a b (b ◇ a) a a))
  have p48:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ c) (p3x a (c ◇ b))).symm).trans ((h b (a ◇ (c ◇ b)) c).symm)).trans (p23 a b c ((b ◇ (a ◇ (c ◇ b))) ◇ c) ((b ◇ (a ◇ (c ◇ b))) ◇ c) ((b ◇ (a ◇ (c ◇ b))) ◇ c))).symm
  have p49:=fun (a b c:G)=>by
    exact (((p44 a (c ◇ b) c a a).symm).trans ((h b ((c ◇ b) ◇ a) c).symm)).symm
  have p4a:=fun (a b c d:G)=>by
    exact ((((((((cg (fun t => t ◇ (((b ◇ (b ◇ a)) ◇ b) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (p3x a b)))))).trans (cg (fun t => t ◇ (((b ◇ (b ◇ a)) ◇ b) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (p45 (a ◇ a) b b ((b ◇ ((a ◇ a) ◇ b)) ◇ b) ((b ◇ ((a ◇ a) ◇ b)) ◇ b)))))).trans (cg (fun t => t ◇ (((b ◇ (b ◇ a)) ◇ b) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (p3y a b (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b))))))).trans (cg (fun t => t ◇ (((b ◇ (b ◇ a)) ◇ b) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (p3y a b (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b)))))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (cg (fun t => t ◇ b) (p45 b a b ((b ◇ (b ◇ a)) ◇ b) ((b ◇ (b ◇ a)) ◇ b))))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (cg (fun t => t ◇ b) (p2o b a)))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (p2o b a))).symm).trans ((((cg (fun t => (d ◇ (((b ◇ ((a ◇ b) ◇ b)) ◇ b) ◇ c)) ◇ t) (p5 a b)).symm).trans ((h c d ((b ◇ ((a ◇ b) ◇ b)) ◇ b)).symm)).trans ((((cg (fun t => (c ◇ d) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => b ◇ t) (p3x a b)))).trans (cg (fun t => (c ◇ d) ◇ t) (p45 (a ◇ a) b b ((b ◇ ((a ◇ a) ◇ b)) ◇ b) ((b ◇ ((a ◇ a) ◇ b)) ◇ b)))).trans (cg (fun t => (c ◇ d) ◇ t) (cg (fun t => t ◇ b) (p3y a b (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b))))).trans (cg (fun t => (c ◇ d) ◇ t) (p3y a b (((a ◇ a) ◇ b) ◇ b) (((a ◇ a) ◇ b) ◇ b)))))
  have p4b:=fun (a b c d e f g i j:G)=>by
    exact (p23 a b c a a a).trans (p48 a b c)
  have p4c:=fun (a b c:G)=>by
    exact (((pf c b a b c).trans (p49 a b c)).symm).trans (((cg (fun t => t ◇ c) (p42 (c ◇ b) a)).symm).trans ((h b (a ◇ a) c).symm))
  have p4d:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (p3v a b c)).symm).trans (p3z c (a ◇ b) a a)
  have p4e:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p3x a b)).symm).trans ((((cg (fun t => t ◇ ((a ◇ b) ◇ b)) (p3x a b)).symm).trans (p3b a b)).trans (cg (fun t => (b ◇ b) ◇ t) (p3x a b)))
  have p4f:=fun (a b c d e f:G)=>by
    exact (p48 a b c).trans (p4c a b c)
  have p4g:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (cg (fun t => (b ◇ b) ◇ t) (p3x a b))).symm).trans ((((cg (fun t => t ◇ c) (p3b a b)).symm).trans (p42 c ((a ◇ b) ◇ b))).trans ((cg (fun t => t ◇ c) (cg (fun t => c ◇ t) (p3x a b))).trans (p45 (a ◇ a) b c ((c ◇ ((a ◇ a) ◇ b)) ◇ c) ((c ◇ ((a ◇ a) ◇ b)) ◇ c))))
  have p4h:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (cg (fun t => (b ◇ c) ◇ t) (p3x a b))).symm).trans (p3c a b c)).trans (cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (p3x a b)))
  have p4i:=fun (a b c d e f g i j k l m:G)=>by
    exact (p4b a b c a a a a a a).trans (p4c a b c)
  have p4j:=fun (a b c:G)=>by
    exact (((p4c a b c).symm).trans ((((cg (fun t => t ◇ c) (p3y a (c ◇ b) a a)).symm).trans ((h b ((a ◇ a) ◇ (c ◇ b)) c).symm)).trans (p4i (a ◇ a) b c ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c) ((b ◇ ((a ◇ a) ◇ (c ◇ b))) ◇ c)))).symm
  have p4k:=fun (a b c:G)=>by
    exact (((p4d a b c).symm).trans ((((cg (fun t => t ◇ (a ◇ b)) (p3u a b c)).symm).trans (p3p c (a ◇ b))).trans (p1p (a ◇ b) c))).symm
  have p4l:=fun (a b c d e f:G)=>by
    exact ((cg (fun t => (c ◇ c) ◇ t) (p3x a b)).symm).trans ((((p4k (a ◇ b) b c).symm).trans (p3a a b c)).trans (cg (fun t => (b ◇ c) ◇ t) (p3x a b)))
  have p4m:=fun (a b c:G)=>by
    exact ((p4f b (b ◇ a) c (((b ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ c) (((b ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ c) (((b ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ c)).symm).trans (((cg (fun t => t ◇ c) (p4l b b a a a a)).symm).trans (p4f b (a ◇ a) c a a a))
  have p4n:=fun (a b c:G)=>by
    exact ((p1p (a ◇ b) (c ◇ c)).symm).trans ((((cg (fun t => t ◇ (a ◇ b)) (p4k a b c)).symm).trans (p2o (a ◇ b) c)).trans (p4k a b c))
  have p4o:=fun (a b c:G)=>by
    exact (((p4n b c a).symm).trans (p4k b c (a ◇ a))).symm
  have p4p:=fun (a b c d e f g i j k l:G)=>by
    exact ((((((cg (fun t => t ◇ c) (p29 b a c)).trans (pt b (c ◇ (b ◇ a)) c)).trans (pt (b ◇ a) b c)).trans (cg (fun t => t ◇ c) (p44 a b c (((b ◇ a) ◇ b) ◇ c) (((b ◇ a) ◇ b) ◇ c)))).symm).trans (((cg (fun t => t ◇ c) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p42 b c))))).symm).trans (p3q a b c a a a a a a))).symm
  have p4q:=fun (a b c:G)=>by
    exact (((pt b a c).symm).trans ((((cg (fun t => t ◇ c) ((h a (c ◇ b) c).symm)).symm).trans (p4p b (c ◇ a) c a a a a a a a a)).trans (cg (fun t => t ◇ c) (p4c b a c)))).symm
  have p4r:=fun (a b c:G)=>by
    exact (((p4q b a c).symm).trans (((cg (fun t => t ◇ c) (p4j a b c)).symm).trans (p4q b (a ◇ a) c))).symm
  have p4s:=fun (a b c d e f:G)=>by
    exact (p4g a b c).trans (p4r a b c)
  have p4t:=fun (a b c d e f:G)=>by
    exact (p4h a b c).trans (p4r a b c)
  have p4u:=fun (a b c:G)=>by
    exact ((p4q a b c).symm).trans ((((cg (fun t => t ◇ c) ((h a (b ◇ b) c).symm)).symm).trans (p4r b (c ◇ a) c)).trans (pt a b c))
  have p4v:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => c ◇ t) (p3x a b))).symm).trans ((h b c (a ◇ b)).symm)
  have p4w:=fun (a b:G)=>by
    exact ((((((p3f b (a ◇ b)).trans (p1p (a ◇ b) b)).trans (cg (fun t => t ◇ (a ◇ b)) (p3x a b))).trans (p46 a b)).symm).trans (((p4v a b (b ◇ b)).symm).trans (p4s a b (a ◇ b) a a a))).symm
  have p4x:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (p4w a b)).symm).trans (p41 (a ◇ b) c a a)).trans ((p42 c (a ◇ b)).trans (p45 a b c ((c ◇ (a ◇ b)) ◇ c) ((c ◇ (a ◇ b)) ◇ c)))
  have p4y:=fun (a b:G)=>by
    exact ((((p4w b a).symm).trans (p4u a b (b ◇ a))).trans (p3x (a ◇ b) (b ◇ a))).symm
  have p4z:=fun (a b c d:G)=>by
    exact ((((((((((((cg (fun t => t ◇ ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (p45 b a a ((a ◇ (b ◇ a)) ◇ a) ((a ◇ (b ◇ a)) ◇ a)))))).trans (cg (fun t => t ◇ ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (cg (fun t => t ◇ a) (p1p a b))))))).trans (cg (fun t => t ◇ ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ b) (p2o a b)))))).trans (cg (fun t => t ◇ ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (p40 (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) a b (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b)))))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (cg (fun t => t ◇ b) (p44 a b (b ◇ a) (((b ◇ a) ◇ b) ◇ (b ◇ a)) (((b ◇ a) ◇ b) ◇ (b ◇ a)))))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (cg (fun t => t ◇ b) (p47 a b)))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (p43 b (b ◇ a) (((b ◇ b) ◇ (b ◇ a)) ◇ b) (((b ◇ b) ◇ (b ◇ a)) ◇ b)))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (p45 b a b ((b ◇ (b ◇ a)) ◇ b) ((b ◇ (b ◇ a)) ◇ b)))).trans (cg (fun t => (d ◇ (((a ◇ a) ◇ b) ◇ c)) ◇ t) (p2o b a))).trans (p4a a b c d)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b)) (cg (fun t => d ◇ t) (cg (fun t => t ◇ c) (p6 a b)))).symm).trans ((h c d ((((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b)).symm)).trans (((((cg (fun t => (c ◇ d) ◇ t) (cg (fun t => t ◇ b) (p44 a b (b ◇ a) (((b ◇ a) ◇ b) ◇ (b ◇ a)) (((b ◇ a) ◇ b) ◇ (b ◇ a))))).trans (cg (fun t => (c ◇ d) ◇ t) (cg (fun t => t ◇ b) (p47 a b)))).trans (cg (fun t => (c ◇ d) ◇ t) (p43 b (b ◇ a) (((b ◇ b) ◇ (b ◇ a)) ◇ b) (((b ◇ b) ◇ (b ◇ a)) ◇ b)))).trans (cg (fun t => (c ◇ d) ◇ t) (p45 b a b ((b ◇ (b ◇ a)) ◇ b) ((b ◇ (b ◇ a)) ◇ b)))).trans (cg (fun t => (c ◇ d) ◇ t) (p2o b a))))).symm
  have p50:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (p4o a b (a ◇ a))).symm).trans (p4x b (a ◇ a) c)).trans ((p4u (a ◇ a) b c).trans (p4r a b c))
  have p51:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ b) (p45 b a a ((a ◇ (b ◇ a)) ◇ a) ((a ◇ (b ◇ a)) ◇ a)))).trans (cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ b) (cg (fun t => t ◇ a) (p1p a b))))).trans (cg (fun t => t ◇ (b ◇ a)) (cg (fun t => t ◇ b) (p2o a b)))).trans (cg (fun t => t ◇ (b ◇ a)) (p40 (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) a b (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b)))).trans (p47 a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ a)) (p6 a b)).symm).trans (p1 (b ◇ a) b (b ◇ a))).trans (((((cg (fun t => t ◇ (b ◇ a)) (p4z a b (b ◇ a) (b ◇ a))).trans (cg (fun t => t ◇ (b ◇ a)) (p4l a b (b ◇ a) (((b ◇ a) ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ b)) (((b ◇ a) ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ b)) (((b ◇ a) ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ b))))).trans (p4t a b (b ◇ a) (((b ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ (b ◇ a)) (((b ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ (b ◇ a)) (((b ◇ (b ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ (b ◇ a)))).trans (p3x (a ◇ b) (b ◇ a))).trans (p4y a b)))
  have p52:=fun (a b:G)=>by
    exact ((p51 b (a ◇ a)).symm).trans (p4o a (a ◇ a) b)
  have p53:=fun (a b c d:G)=>by
    exact (p4e c d).trans (p52 c d)
  have p54:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) (p53 a a a b)).symm).trans (p42 c ((a ◇ a) ◇ b))).trans ((p45 (a ◇ a) b c ((c ◇ ((a ◇ a) ◇ b)) ◇ c) ((c ◇ ((a ◇ a) ◇ b)) ◇ c)).trans (p4r a b c))
  have p55:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ d) (p4f a b (d ◇ c) a a a)).symm).trans ((h c (b ◇ ((a ◇ a) ◇ a)) d).symm)).symm
  have p56:=fun (a b c:G)=>by
    exact (((p55 a c b c).symm).trans ((h ((a ◇ a) ◇ a) b c).symm)).trans (cg (fun t => t ◇ c) (p41 a b (((a ◇ a) ◇ a) ◇ b) (((a ◇ a) ◇ a) ◇ b)))
  have p57:=fun (a b c:G)=>by
    exact ((p4v b c (c ◇ a)).symm).trans (((cg (fun t => t ◇ (b ◇ c)) (p4l b c a a a a)).symm).trans (p4v b c (a ◇ a)))
  have p58:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ c) (p57 a c b)).symm).trans ((h b (b ◇ (b ◇ a)) c).symm)
  have p59:=fun (a b c:G)=>by
    exact ((p58 a b c).symm).trans ((h b (b ◇ (a ◇ a)) c).symm)
  have p5a:=fun (a b c:G)=>by
    exact ((p3r (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a) (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a) (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a) b b c a (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a) (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a) (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a) (((a ◇ (a ◇ (b ◇ b))) ◇ (a ◇ c)) ◇ a)).symm).trans (((cg (fun t => t ◇ a) (p59 b a (a ◇ c))).symm).trans (p3r a a a a b c a a a a a))
  have p5b:=fun (a b c:G)=>by
    exact ((p5a c a (c ◇ b)).symm).trans (p56 a b c)
  have p5c:=fun (a b c:G)=>by
    exact (((p5b a b c).symm).trans ((h b (c ◇ (c ◇ a)) c).symm)).symm
  have p5d:=fun (a b c:G)=>by
    exact (((p5c a b c).symm).trans ((h (c ◇ a) b c).symm)).symm
  have p5e:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ c) ((h a c b).symm)).symm).trans (p5d (b ◇ a) b c)).trans ((((cg (fun t => t ◇ c) (p42 b (b ◇ a))).trans (cg (fun t => t ◇ c) (p45 b a b ((b ◇ (b ◇ a)) ◇ b) ((b ◇ (b ◇ a)) ◇ b)))).trans (cg (fun t => t ◇ c) (p2o b a))).trans (p44 a b c (((b ◇ a) ◇ b) ◇ c) (((b ◇ a) ◇ b) ◇ c)))
  have p5f:=fun (a b c:G)=>by
    exact (((p4c a b c).symm).trans (((p5e a (c ◇ b) c).symm).trans ((h b (a ◇ c) c).symm))).symm
  have p5g:=fun (a b c:G)=>by
    exact (((p4c a b c).symm).trans (((p5d a (c ◇ b) c).symm).trans ((h b (c ◇ a) c).symm))).symm
  have p5h:=fun (a b c:G)=>by
    exact ((p5g a b c).symm).trans ((h a b c).symm)
  have p5i:=fun (a b c d e f:G)=>by
    exact ((p5h (d ◇ d) e f).symm).trans ((p4j d e f).trans (p5h d e f))
  have p5j:=fun (a b c d e f g i j k l:G)=>by
    exact (p44 d e f d d).trans (p5i (((d ◇ d) ◇ e) ◇ f) (((d ◇ d) ◇ e) ◇ f) (((d ◇ d) ◇ e) ◇ f) d e f)
  have p5k:=fun (a b c d e f g i j:G)=>by
    exact (p5d a b c).trans (p5i (((a ◇ a) ◇ b) ◇ c) (((a ◇ a) ◇ b) ◇ c) (((a ◇ a) ◇ b) ◇ c) a b c)
  have p5l:=fun (a b c d e f g i j:G)=>by
    exact (p5e a b c).trans (p5i (((a ◇ a) ◇ b) ◇ c) (((a ◇ a) ◇ b) ◇ c) (((a ◇ a) ◇ b) ◇ c) a b c)
  have p5m:=fun (a b c d e f:G)=>by
    exact ((p5h e (e ◇ d) f).symm).trans ((p4m d e f).trans ((p5h e (d ◇ d) f).trans (p5h d e f)))
  have p5n:=fun (a b c d e f:G)=>by
    exact (p5f a b c).trans (p5h a b c)
  have p5o:=fun (a b c d:G)=>by
    exact (((((((((((((cg (fun t => t ◇ d) (cg (fun t => t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => d ◇ t) (p21 a b a b))))).trans (cg (fun t => t ◇ d) (cg (fun t => t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => d ◇ t) (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p3x a b)))))))).trans (cg (fun t => t ◇ d) (cg (fun t => t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => d ◇ t) (p5n (a ◇ a) a b ((a ◇ ((a ◇ a) ◇ b)) ◇ b) ((a ◇ ((a ◇ a) ◇ b)) ◇ b) ((a ◇ ((a ◇ a) ◇ b)) ◇ b))))))).trans (cg (fun t => t ◇ d) (cg (fun t => t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ b)) (cg (fun t => t ◇ c) (cg (fun t => d ◇ t) (p5i (((a ◇ a) ◇ a) ◇ b) (((a ◇ a) ◇ a) ◇ b) (((a ◇ a) ◇ a) ◇ b) a a b)))))).trans (cg (fun t => t ◇ d) (cg (fun t => ((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ t) (cg (fun t => t ◇ b) (p45 b a a ((a ◇ (b ◇ a)) ◇ a) ((a ◇ (b ◇ a)) ◇ a)))))).trans (cg (fun t => t ◇ d) (cg (fun t => ((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ a) (p1p a b)))))).trans (cg (fun t => t ◇ d) (cg (fun t => ((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ t) (cg (fun t => t ◇ b) (p5j (((a ◇ b) ◇ a) ◇ a) (((a ◇ b) ◇ a) ◇ a) (((a ◇ b) ◇ a) ◇ a) b a a (((a ◇ b) ◇ a) ◇ a) (((a ◇ b) ◇ a) ◇ a) (((a ◇ b) ◇ a) ◇ a) (((a ◇ b) ◇ a) ◇ a) (((a ◇ b) ◇ a) ◇ a)))))).trans (cg (fun t => t ◇ d) (cg (fun t => ((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ t) (cg (fun t => t ◇ b) (p1p a b))))).trans (cg (fun t => t ◇ d) (cg (fun t => ((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ t) (p5j (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) b a b (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b) (((a ◇ b) ◇ a) ◇ b))))).trans (cg (fun t => t ◇ d) (p4z a b (d ◇ ((a ◇ a) ◇ b)) c))).trans (cg (fun t => t ◇ d) (p5l d c ((a ◇ a) ◇ b) (((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ ((a ◇ a) ◇ b)) (((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ ((a ◇ a) ◇ b)) (((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ ((a ◇ a) ◇ b)) (((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ ((a ◇ a) ◇ b)) (((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ ((a ◇ a) ◇ b)) (((d ◇ ((a ◇ a) ◇ b)) ◇ c) ◇ ((a ◇ a) ◇ b))))).trans (p5k c ((a ◇ a) ◇ b) d (((d ◇ c) ◇ ((a ◇ a) ◇ b)) ◇ d) (((d ◇ c) ◇ ((a ◇ a) ◇ b)) ◇ d) (((d ◇ c) ◇ ((a ◇ a) ◇ b)) ◇ d) (((d ◇ c) ◇ ((a ◇ a) ◇ b)) ◇ d) (((d ◇ c) ◇ ((a ◇ a) ◇ b)) ◇ d) (((d ◇ c) ◇ ((a ◇ a) ◇ b)) ◇ d))).symm).trans ((((cg (fun t => t ◇ d) (cg (fun t => ((d ◇ ((a ◇ ((b ◇ a) ◇ b)) ◇ b)) ◇ c) ◇ t) (p7 a b))).symm).trans (p1 c ((a ◇ ((b ◇ a) ◇ b)) ◇ b) d)).trans (((((((cg (fun t => t ◇ d) (cg (fun t => (c ◇ d) ◇ t) (cg (fun t => d ◇ t) (p21 a b a b)))).trans (cg (fun t => t ◇ d) (cg (fun t => (c ◇ d) ◇ t) (cg (fun t => d ◇ t) (cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p3x a b))))))).trans (cg (fun t => t ◇ d) (cg (fun t => (c ◇ d) ◇ t) (cg (fun t => d ◇ t) (p5n (a ◇ a) a b ((a ◇ ((a ◇ a) ◇ b)) ◇ b) ((a ◇ ((a ◇ a) ◇ b)) ◇ b) ((a ◇ ((a ◇ a) ◇ b)) ◇ b)))))).trans (cg (fun t => t ◇ d) (cg (fun t => (c ◇ d) ◇ t) (cg (fun t => d ◇ t) (p5i (((a ◇ a) ◇ a) ◇ b) (((a ◇ a) ◇ a) ◇ b) (((a ◇ a) ◇ a) ◇ b) a a b))))).trans (pa (((c ◇ d) ◇ (d ◇ ((a ◇ a) ◇ b))) ◇ d) (((c ◇ d) ◇ (d ◇ ((a ◇ a) ◇ b))) ◇ d) (((c ◇ d) ◇ (d ◇ ((a ◇ a) ◇ b))) ◇ d) (((c ◇ d) ◇ (d ◇ ((a ◇ a) ◇ b))) ◇ d) (((c ◇ d) ◇ (d ◇ ((a ◇ a) ◇ b))) ◇ d) a a b (c ◇ d) d)).trans (cg (fun t => t ◇ d) (p5i (((a ◇ a) ◇ b) ◇ (c ◇ d)) (((a ◇ a) ◇ b) ◇ (c ◇ d)) (((a ◇ a) ◇ b) ◇ (c ◇ d)) a b (c ◇ d)))).trans (p5n c (a ◇ b) d (((a ◇ b) ◇ (c ◇ d)) ◇ d) (((a ◇ b) ◇ (c ◇ d)) ◇ d) (((a ◇ b) ◇ (c ◇ d)) ◇ d))))
  have p5p:=fun (a b c d e f g i j:G)=>by
    exact ((p5i (((g ◇ g) ◇ (i ◇ (g ◇ g))) ◇ j) (((g ◇ g) ◇ (i ◇ (g ◇ g))) ◇ j) (((g ◇ g) ◇ (i ◇ (g ◇ g))) ◇ j) g (i ◇ (g ◇ g)) j).symm).trans (p50 g i j)
  have p5q:=fun (a b c d e f g i j:G)=>by
    exact ((((p5o a b a c).trans (p5m ((a ◇ (a ◇ b)) ◇ c) ((a ◇ (a ◇ b)) ◇ c) ((a ◇ (a ◇ b)) ◇ c) b a c)).symm).trans (((p5i (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ c) (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ c) (((a ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ c) a ((a ◇ a) ◇ b) c).symm).trans (p54 a b c))).symm
  have p5r:=fun (a b c d e f g i j k l m:G)=>by
    exact (((p5q b a c (((b ◇ a) ◇ c) ◇ c) (((b ◇ a) ◇ c) ◇ c) (((b ◇ a) ◇ c) ◇ c) (((b ◇ a) ◇ c) ◇ c) (((b ◇ a) ◇ c) ◇ c) (((b ◇ a) ◇ c) ◇ c)).symm).trans ((p4u a b c).trans (p5q a b c (((a ◇ b) ◇ c) ◇ c) (((a ◇ b) ◇ c) ◇ c) (((a ◇ b) ◇ c) ◇ c) (((a ◇ b) ◇ c) ◇ c) (((a ◇ b) ◇ c) ◇ c) (((a ◇ b) ◇ c) ◇ c)))).symm
  have p5s:=fun (a b c d e f g i j k l m:G)=>by
    exact ((((p5r (l ◇ (k ◇ k)) k m ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m) ((k ◇ (l ◇ (k ◇ k))) ◇ m)).trans (cg (fun t => t ◇ m) (p5r (k ◇ k) l k ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k) ((l ◇ (k ◇ k)) ◇ k)))).trans (cg (fun t => t ◇ m) (p5i (((k ◇ k) ◇ l) ◇ k) (((k ◇ k) ◇ l) ◇ k) (((k ◇ k) ◇ l) ◇ k) k l k))).symm).trans (((p5p k k k k k k k l m).trans (p5q k l m (((k ◇ l) ◇ m) ◇ m) (((k ◇ l) ◇ m) ◇ m) (((k ◇ l) ◇ m) ◇ m) (((k ◇ l) ◇ m) ◇ m) (((k ◇ l) ◇ m) ◇ m) (((k ◇ l) ◇ m) ◇ m))).trans (p5r k l m ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m) ((l ◇ k) ◇ m)))
  exact (calc
    ((x ◇ y) ◇ z)=((x ◇ y) ◇ z):=rfl
    _=(((y ◇ x) ◇ x) ◇ z):=((cg (fun t => t ◇ z) (p5r x y x ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x) ((y ◇ x) ◇ x))).trans (p5s (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) (((x ◇ y) ◇ x) ◇ z) x y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_61441_to_62284 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_61441_to_62284
