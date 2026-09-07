-- Equation1722 → Equation3143
-- Recorded verdict: false
-- Premise: x = (y ◇ y) ◇ ((x ◇ y) ◇ y)
-- Conclusion: x = (((y ◇ y) ◇ x) ◇ y) ◇ y
-- Original submission SHA-256: e70d8a8ae5853e1755145360b852bb721f89a99a676e1fe7c4d0f9e3b622d1fb
-- Aurora-accepted correction SHA-256: 54a2f7c2f4eedc73981403d7dc63a12e54c9088e842c94058bf1e35f6304681e
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.AList
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ y) ◇ ((x ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ y) ◇ x) ◇ y) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                                
                            
                              
                              
                                      
                     
set_option maxHeartbeats 0
namespace submission
namespace List
variable {α: Type*}
instance decidableChain {R: α→α→Prop} [DecidableRel R] (l: List α):
  Decidable (_root_.List.IsChain R l):=by
 induction l with
 | nil=>exact .isTrue .nil
 | cons a as ih=>exact decidable_of_iff' _ List.isChain_cons
end List
theorem Exists.cr {α: Sort*} {p: α→Prop} (h:∃ a,p a)
  {C: Sort*} (H:∀ a,p a→C):∃ a pa,h.classicalRecOn H=H a pa:=⟨_,_,rfl⟩
theorem chain {α β: Type*} [Preorder α] [Countable β]
  (task: β→Set α) (H:∀ a b,∃ a',a≤a'∧a'∈task b) (a: α):∃ c,IsChain (·≤·) c∧a∈c∧(∀ x∈c,a≤x)∧∀ b,∃ a∈c,a∈task b:=by
 have⟨f,hf⟩:=exists_surjective_nat (Option β)
 let T:=Σ a',{c // a'∈c∧IsChain (·≤·) c∧∀ x∈c,a≤x∧x≤a'}
 let G: Nat→T→T:=fun n⟨a',c,ac,hc,hl⟩=>match f n with
  | none=>⟨a',c,ac,hc,hl⟩
  | some b=>by
   refine (H a' b).classicalRecOn fun a''⟨a'a'',_⟩=>?_
   refine⟨a'',insert a'' c,by simp,IsChain.insert hc ?_,?_⟩
   · exact fun d dc _=>.inr (le_trans (hl _ dc).2 a'a'')
   · refine Set.forall_mem_insert.2 ⟨⟨le_trans (hl _ ac).1 a'a'',le_rfl⟩,?_⟩
     exact fun d dc=>(hl _ dc).imp_right (le_trans · a'a'')
 let F: Nat→Σ a',{c // a'∈c∧IsChain (·≤·) c∧∀ x∈c,a≤x∧x≤a'}:=Nat.rec ⟨a,{a},rfl,Set.subsingleton_singleton.isChain,by simp⟩ G
 have hF i: F (i+1)=G i (F i):=rfl
 have: Monotone (fun i=>(F i).2.1):=monotone_nat_of_le_succ fun n=>by
  rw [hF]; obtain⟨a',c,ac,hc,hl⟩:=F n
  simp only [G]; split<;>simp only [le_refl]
  exact let⟨a,ha,eq⟩:=Exists.cr _ _; eq▸ by cases ha; simp
 refine⟨⋃ i,(F i).2.1,?_,?_,?_,fun b=>?_⟩
 · rintro a⟨_,⟨i,rfl⟩,hi⟩ b⟨_,⟨j,rfl⟩,hj⟩ ab; simp at hi hj⊢
   exact (F (max i j)).2.2.2.1 (this (le_max_left i j) hi) (this (le_max_right i j) hj) ab
 · refine⟨_,⟨0,rfl⟩,rfl⟩
 · rintro a'⟨_,⟨i,rfl⟩,h⟩; exact ((F i).2.2.2.2 _ h).1
 · clear_value F
   have⟨i,hi⟩:=hf (some b)
   specialize hF i; simp only [G] at hF
   revert hF; obtain⟨a',c,ac,hc,hl⟩:=F i; simp [hi]
   refine let⟨a,ha,eq⟩:=Exists.cr _ _; eq▸ ?_
   obtain⟨h1,h2⟩:=ha; simp; intro hF
   refine⟨a,⟨i+1,?_⟩,h2⟩
   rw [hF]; simp
namespace AdjoinFresh
universe u
variable {α: Type u} [Countable α]
private noncomputable def e:ℕ≃ℕ⊕ α:=Classical.choice (inferInstance: Nonempty (ℕ≃ℕ⊕ α))
noncomputable def adj (m:ℕ):ℕ≃ℕ⊕ α where
 toFun n:=if n<m then .inl n else match e (n - m) with
  | .inl k=>.inl (k + m)
  | .inr c=>.inr c
 invFun
  | .inl k=>if k<m then k else e.symm (.inl (k-m)) + m
  | .inr c=>e.symm (.inr c) + m
 left_inv n:=by
  dsimp
  by_cases h: n<m
  · simp [h]
  · cases h':(e (α:=α) (n-m))<;>simp [h,h']<;>rw [←h']<;>simp<;>omega
 right_inv a:=by
  cases a
  case inl n=>simp only; by_cases h:n<m <;> simp [h] <;> omega
  case inr=>simp
end AdjoinFresh
namespace PartialMagma
abbrev P (α: Type):=α→α→Set α
abbrev Equiv.mv {α β: Type} (e: α≃ β) (E: P β): P α:=fun a b=>{c | e c∈E (e a) (e b)}
class R where
 laws:∀ {α: Type},P α→Prop
 laws_equiv {α β: Type} (e: α≃ β) (E: P β) (ok: laws E): laws (Equiv.mv e E)
structure P.OK [r: R] {α: Type} (E: P α): Prop where
 finite: Set.Finite {x: (α×α)×α | x.2∈E x.1.1 x.1.2}
 func {x y}: Set.Subsingleton (E x y)
 laws: R.laws E
def Equiv.mvOK [R] {α β: Type} (e: α≃ β) (E: P β) (ok: E.OK):
 (Equiv.mv e E).OK where
  finite:=by
   apply ok.finite.of_equiv
   constructor
   case toFun=>refine fun ⟨((a,b),c),h⟩=>⟨((e.symm a,e.symm b),e.symm c),by simpa⟩
   case invFun=>refine fun ⟨((a,b),c),h⟩=>⟨((e a,e b),e c),by simpa⟩
   case left_inv=>refine fun ⟨((a,b),c),h⟩=>?_; simp_all
   case right_inv=>refine fun ⟨((a,b),c),h⟩=>?_; simp_all
  func {x y} z hz z' hz':=by simpa using ok.func hz hz'
  laws:=R.laws_equiv e E ok.laws
open R
abbrev Ext (α: Type) [R]:={E: P α // E.OK}
class B [R]  where
 E: P ℕ
 ok: E.OK
 a:ℕ
 b:ℕ
 ndf {c}: c∉E a b
namespace B
variable [R] [B]
structure Sol (F: Type) (E': P (ℕ⊕ F)): Prop where
 base {a b c}: c∈E a b→(.inl c)∈E' (.inl a) (.inl b)
 ok: P.OK E' (α:=(ℕ⊕ F))
 ab_def: (E' (.inl a) (.inl b)).Nonempty
abbrev FE (F: Type):={E': P (ℕ⊕ F) // Sol F E'}
noncomputable def dom: Finset ℕ:=insert a<| insert b<| ok.finite.toFinset.biUnion fun ((a,b),c)=>{a,b,c}
theorem md {a b c x}
  (h1: c∈E a b) (h2: x∈({a,b,c}: Finset ℕ)): x∈dom:=by
 refine Finset.mem_insert_of_mem<| Finset.mem_insert_of_mem ?_
 simp only [Finset.mem_biUnion,Set.Finite.mem_toFinset,Set.mem_setOf_eq,Prod.exists]
 exact⟨_,_,_,h1,h2⟩
@[scoped aesop safe forward]
theorem dl {a b c} (h: c∈E a b): a∈dom:=md h (by simp)
@[scoped aesop safe forward]
theorem dr {a b c} (h: c∈E a b): b∈dom:=md h (by simp)
@[scoped aesop safe forward]
theorem dout {a b c} (h: c∈E a b): c∈dom:=md h (by simp)
@[scoped aesop safe forward]
theorem da: a∈dom:=Finset.mem_insert_self ..
@[scoped aesop safe forward]
theorem dbb: b∈dom:=Finset.mem_insert_of_mem<| Finset.mem_insert_self ..
noncomputable def db:=dom.sup id + 1
theorem ldb {x} (h: x∈dom): x<db:=Nat.lt_succ_iff.2 (dom.le_sup (f:=id) h)
namespace FE
variable {F: Type} [Countable F] (E': FE F)
open AdjoinFresh
def j: P ℕ:=Equiv.mv (adj db) E'.1
theorem ao: E'.j.OK:=Equiv.mvOK (adj db) E'.1 E'.2.ok
theorem al: E≤E'.j:=by
 intro a b c h
 unfold j Equiv.mv
 simp only [Set.mem_setOf_eq]
 unfold adj
 simp only [Equiv.coe_fn_mk,ldb (dl h),↓reduceIte,ldb (dr h),ldb (dout h)]
 exact E'.2.base h
theorem aab:
 E'.j∈{e: (P ℕ) | Nonempty (e a b)}:=by
 obtain⟨c,c_mem⟩:=E'.2.ab_def
 use ((adj db).symm c)
 unfold j Equiv.mv
 simp only [Set.mem_setOf_eq,Equiv.apply_symm_apply]
 unfold adj
 simp [ldb da,ldb dbb,c_mem]
end FE
end B
end PartialMagma
namespace EQ
namespace Greedy
noncomputable section
open AdjoinFresh PartialMagma
structure Laws {α: Type} (E: P α): Prop where
 eq1722 {x y xy xyy}: xy∈E x y→xyy∈E xy y→∃yy,yy∈E y y∧x∈E yy xyy
 law2 {x y z xy zy}: xy∈E x y→zy∈E z y→xy=zy→x=z
 law3 {x xx}: xx∈E x x→∃ xxx,∃ xxxx,xxx∈E xx x∧xxxx∈E xxx x
 law4 {x z zx}: zx∈E z x→zx=x→∃ xx,xx∈E x x
def leq {α β: Type} (e: α≃ β) (E: P β) (ok: Laws E):
 Laws (Equiv.mv e E) where
 eq1722 xy_mem xyy_mem:=by
  obtain⟨yy,yy_mem,eq⟩:=ok.eq1722 xy_mem xyy_mem
  exact⟨e.symm yy,by simpa using yy_mem,by simpa using eq⟩
 law2 xy_mem zy_mem eq:=by simpa using ok.law2 xy_mem zy_mem (by simpa using eq)
 law3 xx_mem:=by
  obtain⟨xxx,xxxx,h⟩:=ok.law3 xx_mem
  exact⟨e.symm xxx,e.symm xxxx,by simpa using h⟩
 law4 zx_mem eq:=by
  obtain⟨xx,xx_mem⟩:=ok.law4 zx_mem (by simpa using eq)
  exact⟨e.symm xx,by simpa using xx_mem⟩
scoped instance: R where
 laws:=Laws
 laws_equiv:=leq
class C1 extends B where
 b_eq_a: b=a
namespace C1
variable [C1]
inductive F
 | ai: Fin 4→F
 | b₀: F
 | bi: Fin 4→F
 deriving DecidableEq,Fintype
open F
open B
inductive Next:ℕ⊕ F→ℕ⊕ F→ℕ⊕ F→Prop
 | base {x y z}: z∈E x y→Next (.inl x) (.inl y) (.inl z)
 | new: Next (.inl a) (.inl a) (.inr $ ai 0)
 | sq_0: Next (.inr $ ai 0) (.inr $ ai 0) (.inr $ ai 1)
 | sq_1: Next (.inr $ ai 1) (.inr $ ai 1) (.inr $ ai 2)
 | sq_2: Next (.inr $ ai 2) (.inr $ ai 2) (.inr $ ai 3)
 | sq_3: Next (.inr $ ai 3) (.inr $ ai 3) (.inr $ ai 0)
 | e1b: Next (.inr $ ai 0) (.inl a) (.inr b₀)
 | e10: Next (.inr $ ai 1) (.inr $ ai 0) (.inr $ bi 0)
 | e11: Next (.inr $ ai 2) (.inr $ ai 1) (.inr $ bi 1)
 | e12: Next (.inr $ ai 3) (.inr $ ai 2) (.inr $ bi 2)
 | e13: Next (.inr $ ai 0) (.inr $ ai 3) (.inr $ bi 3)
 | e2b: Next (.inr b₀) (.inl a) (.inr $ ai 1)
 | e20: Next (.inr $ bi 0) (.inr $ ai 0) (.inr $ ai 2)
 | e21: Next (.inr $ bi 1) (.inr $ ai 1) (.inr $ ai 3)
 | e22: Next (.inr $ bi 2) (.inr $ ai 2) (.inr $ ai 0)
 | e23: Next (.inr $ bi 3) (.inr $ ai 3) (.inr $ ai 1)
 | e30: Next (.inr $ ai 2) (.inr $ ai 0) (.inr $ ai 0)
 | e31: Next (.inr $ ai 3) (.inr $ ai 1) (.inr $ ai 1)
 | e32: Next (.inr $ ai 0) (.inr $ ai 2) (.inr $ ai 2)
 | e33: Next (.inr $ ai 1) (.inr $ ai 3) (.inr $ ai 3)
 | e40: Next (.inr $ ai 0) (.inr $ ai 1) (.inr $ ai 0)
 | e41: Next (.inr $ ai 1) (.inr $ ai 2) (.inr $ ai 1)
 | e42: Next (.inr $ ai 2) (.inr $ ai 3) (.inr $ ai 2)
 | e43: Next (.inr $ ai 3) (.inr $ ai 0) (.inr $ ai 3)
 | e5b: Next (.inr $ ai 0) (.inr b₀) (.inl a)
 | e50: Next (.inr $ ai 1) (.inr $ bi 0) (.inr $ ai 0)
 | e51: Next (.inr $ ai 2) (.inr $ bi 1) (.inr $ ai 1)
 | e52: Next (.inr $ ai 3) (.inr $ bi 2) (.inr $ ai 2)
 | e53: Next (.inr $ ai 0) (.inr $ bi 3) (.inr $ ai 3)
@[scoped aesop safe destruct]
theorem ndf' {c}: c∉E a a:=b_eq_a▸ ndf (c:=c)
abbrev n: P (ℕ⊕ F):=fun a b=>{c | Next a b c}
theorem nf:∀ {x y},Set.Subsingleton (n x y):=by
 intro x y z z_mem z' z'_mem
 cases z_mem<;>cases z'_mem<;>try rfl
 case base.base x y z z_mem z' z'_mem=>congr; exact ok.func z_mem z'_mem
 all_goals exfalso; apply ndf'; assumption
theorem nl2 {x y z xy zy}: xy∈n x y→zy∈n z y→xy=zy→x=z:=by
 intro xy_mem zy_mem eq
 rw [eq] at xy_mem
 cases xy_mem<;>cases zy_mem
 case base.base xy_mem _ zy_mem=>simp only [Sum.inl.injEq]; exact ok.laws.law2 xy_mem zy_mem rfl
 all_goals rfl
theorem nl3 {x xx}: xx∈n x x→∃ xxx,∃ xxxx,xxx∈n xx x∧xxxx∈n xxx x
 | .base h=>by obtain⟨u,v,hu,hv⟩:=ok.laws.law3 h; exact⟨.inl u,.inl v,.base hu,.base hv⟩
 | .new=>⟨.inr b₀,.inr (ai 1),.e1b,.e2b⟩
 | .sq_0=>⟨.inr (bi 0),.inr (ai 2),.e10,.e20⟩
 | .sq_1=>⟨.inr (bi 1),.inr (ai 3),.e11,.e21⟩
 | .sq_2=>⟨.inr (bi 2),.inr (ai 0),.e12,.e22⟩
 | .sq_3=>⟨.inr (bi 3),.inr (ai 1),.e13,.e23⟩
theorem ne {x y xy xyy}: xy∈n x y→xyy∈n xy y→∃yy,yy∈n y y∧x∈n yy xyy
 | .base h,.base k=>by obtain⟨u,hu,hv⟩:=ok.laws.eq1722 h k; exact⟨.inl u,.base hu,.base hv⟩
 | .base h,.new=>by obtain⟨u,hu⟩:=ok.laws.law4 h rfl; exact (ndf' hu).elim
 | .new,.e1b=>⟨.inr (ai 0),.new,.e5b⟩
 | .sq_0,.e10=>⟨.inr (ai 1),.sq_0,.e50⟩
 | .sq_1,.e11=>⟨.inr (ai 2),.sq_1,.e51⟩
 | .sq_2,.e12=>⟨.inr (ai 3),.sq_2,.e52⟩
 | .sq_3,.e13=>⟨.inr (ai 0),.sq_3,.e53⟩
 | .e1b,.e2b=>⟨.inr (ai 0),.new,.e40⟩
 | .e10,.e20=>⟨.inr (ai 1),.sq_0,.e41⟩
 | .e11,.e21=>⟨.inr (ai 2),.sq_1,.e42⟩
 | .e12,.e22=>⟨.inr (ai 3),.sq_2,.e43⟩
 | .e13,.e23=>⟨.inr (ai 0),.sq_3,.e40⟩
 | .e20,.e30=>⟨.inr (ai 1),.sq_0,.e10⟩
 | .e21,.e31=>⟨.inr (ai 2),.sq_1,.e11⟩
 | .e22,.e32=>⟨.inr (ai 3),.sq_2,.e12⟩
 | .e23,.e33=>⟨.inr (ai 0),.sq_3,.e13⟩
 | .e30,.sq_0=>⟨.inr (ai 1),.sq_0,.sq_1⟩
 | .e31,.sq_1=>⟨.inr (ai 2),.sq_1,.sq_2⟩
 | .e32,.sq_2=>⟨.inr (ai 3),.sq_2,.sq_3⟩
 | .e33,.sq_3=>⟨.inr (ai 0),.sq_3,.sq_0⟩
 | .e40,.e40=>⟨.inr (ai 2),.sq_1,.e30⟩
 | .e41,.e41=>⟨.inr (ai 3),.sq_2,.e31⟩
 | .e42,.e42=>⟨.inr (ai 0),.sq_3,.e32⟩
 | .e43,.e43=>⟨.inr (ai 1),.sq_0,.e33⟩
theorem nl4 {x z zx}: zx∈n z x→zx=x→∃ xx,xx∈n x x:=by
 intro h q; rw [q] at h; cases h with
 | base h=>obtain⟨u,hu⟩:=ok.laws.law4 h rfl; exact⟨.inl u,.base hu⟩
 | e30=>exact⟨.inr (ai 1),.sq_0⟩
 | e31=>exact⟨.inr (ai 2),.sq_1⟩
 | e32=>exact⟨.inr (ai 3),.sq_2⟩
 | e33=>exact⟨.inr (ai 0),.sq_3⟩
def df: Finset (ℕ⊕F):=Finset.image (.inl) dom∪ Finset.image (.inr) Finset.univ
theorem no: n.OK where
 finite:=by
  apply Set.Finite.subset (s:=(↑((df ×ˢ df) ×ˢ df) : Set _)) (Finset.finite_toSet _)
  refine fun ((x,y),z) hx=>?_
  unfold df
  simp at hx⊢; cases hx with
  | base h=>simp [dout h,dl h,dr h]
  | _=>simp [da]
 func {x y xy} hxy {xy'} hxy':=nf hxy hxy'
 laws:={law2:=nl2,eq1722:=ne,law3:=nl3,law4:=nl4}
def ns: Sol F Next where
 base:=Next.base
 ok:=no
 ab_def:=⟨.inr (ai 0),b_eq_a▸ Next.new⟩
end C1
class C2 extends B where
  a_ne_b: a≠ b
  bb:ℕ
  bb_mem: bb∈E b b
namespace C2
variable [C2]
open B
attribute [scoped aesop safe destruct] a_ne_b
@[scoped aesop safe destruct]
theorem a_ne_bbb: a∉E bb b:=by
 intro h
 obtain⟨bbb,bbbb,bbb_mem,eq⟩:=ok.laws.law3 bb_mem
 obtain a_eq_bbb:=ok.func h bbb_mem
 exact ndf (a_eq_bbb▸ eq)
inductive V:ℕ→Prop
 | mk {d}: a∈E d b→V d
theorem V.unique {d d'}: V d→V d'→d=d'
 | .mk h1,.mk h2=>ok.laws.law2 h1 h2 rfl
theorem V.ne_bb {d}: V d→bb≠ d
 | .mk h,rfl=>a_ne_bbb h
inductive Next:ℕ⊕ Unit→ℕ⊕ Unit→ℕ⊕ Unit→Prop
 | base {x y z}: z∈E x y→Next (.inl x) (.inl y) (.inl z)
 | new: Next (.inl a) (.inl b) (.inr ())
 | extra {d}: V d→Next (.inl bb) (.inr ()) (.inl d)
abbrev n: P (ℕ⊕ Unit):=fun a b=>{c | Next a b c}
theorem nf:∀ {x y},Set.Subsingleton (n x y):=by
 intro x y z z_mem z' z'_mem
 cases z_mem<;>generalize ha: a=a' at *<;>generalize hb: b=b' at *<;>generalize hbb: bb=bb' at *<;>cases z'_mem<;>try rfl
 case base.base x y z z_mem z' z'_mem=>congr; exact ok.func z_mem z'_mem
 case extra.extra=>simp only [Sum.inl.injEq]; apply V.unique<;>assumption
 all_goals rw [← ha,← hb,← hbb] at *
 all_goals exfalso; apply ndf; assumption
theorem nl2 {x y z xy zy}: xy∈n x y→zy∈n z y→xy=zy→x=z:=by
 intro xy_mem zy_mem eq
 rw [eq] at xy_mem
 cases xy_mem<;>cases zy_mem
 case base.base xy_mem _ zy_mem=>simp only [Sum.inl.injEq]; exact ok.laws.law2 xy_mem zy_mem rfl
 all_goals rfl
theorem nl3' {x y xx}: x=y→xx∈n x y→∃ xxx,∃ xxxx,xxx∈n xx x∧xxxx∈n xxx x:=by
 intro x_eq_y xx_mem
 cases xx_mem with
 | base h=>simp only [Sum.inl.injEq] at x_eq_y; rw [←x_eq_y] at h; obtain⟨u,v,hu,hv⟩:=ok.laws.law3 h; exact⟨.inl u,.inl v,.base hu,.base hv⟩
 | new=>injection x_eq_y with hab; exact (a_ne_b hab).elim
 | extra=>contradiction
theorem ne {x y xy xyy}: xy∈n x y→xyy∈n xy y→∃yy,yy∈n y y∧x∈n yy xyy:=by
 intro xy_mem xyy_mem
 cases xy_mem<;>cases xyy_mem
 case base.base xy_mem _ xyy_mem=>obtain⟨yy,yy_mem,eq⟩:=ok.laws.eq1722 xy_mem xyy_mem; exact⟨.inl yy,.base yy_mem,.base eq⟩
 case base.new h=>exact⟨.inl bb,.base bb_mem,.extra (.mk h)⟩
 case extra.extra h=>exact (h.ne_bb rfl).elim
theorem nl4 {x z zx}: zx∈n z x→zx=x→∃ xx,xx∈n x x:=by
 intro zx_mem eq
 rw [eq] at zx_mem
 cases zx_mem
 case base h=>obtain⟨xx,xx_mem⟩:=(ok.laws.law4 h rfl); exact⟨.inl xx,.base xx_mem⟩
def df: Finset (ℕ⊕ Unit):=Finset.image (.inl) dom∪ Finset.image (.inr) Finset.univ
theorem no: n.OK where
 finite:=by
  apply Set.Finite.subset (s:=(↑((df ×ˢ df) ×ˢ df) : Set _)) (Finset.finite_toSet _)
  refine fun ((x,y),z) hx=>?_
  unfold df
  simp at hx⊢; cases hx with
  | base h=>simp [dout h,dl h,dr h]
  | new=>simp [da,dbb]
  | extra h=>simp [dl h.1,dout bb_mem]
 func {x y xy} hxy {xy'} hxy':=nf hxy hxy'
 laws:={law2:=nl2,eq1722:=ne,law3:=nl3' rfl,law4:=nl4}
def ns: Sol Unit Next where
 base:=Next.base
 ok:=no
 ab_def:=⟨.inr (),Next.new⟩
end C2
open B
theorem liftS:∀ (E: Ext ℕ) (a:ℕ),∃ E': Ext ℕ,E≤E'∧E'∈{e: Ext ℕ  | (e.1 a a).Nonempty}:=fun ⟨E,ok⟩ a=>by
 if h: (E a a).Nonempty then exact⟨_,le_rfl,h⟩ else
 let E1: C1:={E,ok,a,b:=a,ndf:=(fun h'=>h ⟨_,h'⟩),b_eq_a:=rfl}
 letI : B:=E1.toB
 let FE: FE _:=⟨_,E1.ns⟩
 obtain⟨⟨x,hx⟩⟩:=(@B.FE.aab _ E1.toB _ _ FE)
 exact⟨⟨FE.j,FE.ao⟩,FE.al,⟨x,hx⟩⟩
theorem lift:∀ (E: Ext ℕ) (a b:ℕ),∃ E': Ext ℕ,E≤E'∧E'∈{e: Ext ℕ | (e.1 a b).Nonempty}:=fun ⟨E,ok⟩ a b=>by
 if h: (E a b).Nonempty then exact⟨_,le_rfl,h⟩ else
 if b_eq_a: b=a then exact b_eq_a▸ liftS ⟨E,ok⟩ a else
 obtain⟨E',le,⟨bb,bb_mem⟩⟩:=liftS ⟨E,ok⟩ b
 if h': (E'.1 a b).Nonempty then exact⟨E',le,h'⟩ else
 let E2: C2:={E:=E'.1,ok:=E'.2,a,b,ndf:=(fun h''=>h' ⟨_,h''⟩),bb,bb_mem,a_ne_b:=by tauto}
 letI : B:=E2.toB
 let FE: FE _:=⟨_,E2.ns⟩
 obtain⟨⟨x,hx⟩⟩:=(@B.FE.aab _ E2.toB _ _ FE)
 exact⟨⟨FE.j,FE.ao⟩,le_trans le FE.al,⟨x,hx⟩⟩
variable (e₀: Ext ℕ)
theorem total:∃ op:ℕ→ℕ→ℕ,(∀ x y,x=op (op y y) (op (op x y) y))∧(∀ {x y z},z∈e₀.1 x y→z=op x y):=by
 classical
 have⟨c,hc,h1,h2,h3⟩:=chain (a:=e₀)
  (task:=fun x: _×_=>{e | (e.1 x.1 x.2).Nonempty}) fun ⟨E,ok⟩⟨a,b⟩=>by
   apply lift
 simp only [Subtype.exists,Prod.forall] at h3
 classical
 choose f hf1 hf2 op hop using h3
 refine⟨op,fun x y=>?_,fun {x y z} H=>?_⟩
 · let S: Finset _:={(y,y),(x,y),(op x y,y),(op y y,op (op x y) y)}
   have⟨⟨e,he⟩,le⟩:=hc.directed.finset_le (hι:=⟨⟨_,h1⟩⟩)
    (S.image fun (a,b)=>⟨⟨f a b,hf1 a b⟩,hf2 a b⟩)
   replace le a (ha: a∈S):=Finset.forall_mem_image.1 le ha _ _ (hop a.1 a.2)
   simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,S] at le
   obtain⟨yy,xy,xyy,final⟩:=le
   obtain⟨yy',yy'_def,eq⟩:=(e.2.laws.eq1722 xy xyy)
   exact e.2.func eq ((e.2.func yy yy'_def)▸ final)
 · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)
def GM (_: Ext ℕ):=ℕ
instance (n): OfNat (GM e₀) n:=inferInstanceAs (OfNat Nat n)
noncomputable instance instMagma: Magma (GM e₀) where
 op:=(total e₀).choose
theorem _root_.submission.PartialMagma.Ext.eq1722: EquationLHS (GM e₀):=(total e₀).choose_spec.1
theorem Ext.base:∀ {x y z: GM e₀},z∈e₀.1 x y→z=x◇ y:=(total e₀).choose_spec.2
def fl (S: List ((Nat×Nat)×Nat)): P ℕ:=fun a b=>{c | ((a,b),c)∈S}
theorem flOK {S: List ((Nat ×ₗ Nat)×Nat)}
  (sorted: S.IsChain (fun a b=>a.1<b.1):=by decide)
  (eq1722:∀ a∈S,∀ b∈S,a.1.2=b.1.2→a.2=b.1.1→∃ c∈S,∃ d∈S,c.1.1=a.1.2∧c.1.2=a.1.2∧d.1.1=c.2∧d.1.2=b.2∧d.2=a.1.1:=by decide)
  (law2:∀ a∈S,∀ b∈S,a.1.2=b.1.2→a.2=b.2→a.1.1=b.1.1:=by decide)
  (law3:∀ a∈S,a.1.1=a.1.2→∃ b∈S,∃ c∈S,b.1.1=a.2∧b.1.2=a.1.1∧c.1.1=b.2∧c.1.2=a.1.1:=by decide)
  (law4:∀ a∈S,a.1.2=a.2→∃ b∈S,b.1.1=a.1.2∧b.1.2=a.1.2:=by decide):
  (fl S).OK where
  finite:=List.finite_toSet S
  func h1 _ h2:=Decidable.by_contra fun h=>have: IsTrans ((ℕ ×ₗℕ) ×ℕ) (·.1<·.1):=⟨fun _ _ _=>lt_trans⟩
   letI:Std.Symm (fun a b:((ℕ ×ₗℕ)×ℕ)=>a.1≠b.1):=⟨fun _ _ h=>h.symm⟩
   (List.isChain_iff_pairwise.1 sorted) |>.imp (fun h=>h.ne) |>.forall h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  laws:={
   eq1722:=fun h1 h2=>by
    obtain⟨⟨⟨y,y'⟩,yy⟩,yy_mem,⟨⟨yy',xyy⟩,x⟩,eq_mem,y_def,y'_def,yy'_def,xyy_def,x_def⟩:=eq1722 _ h1 _ h2 rfl rfl
    simp only at yy_mem eq_mem y_def y'_def yy_mem yy'_def xyy_def x_def
    exists yy
    rewrite [y_def,y'_def] at yy_mem
    use yy_mem
    use yy'_def▸xyy_def▸x_def▸eq_mem
   law2:=fun h h' eq=>law2 _ h _ h' (by simp) (by simpa)
   law3:=fun h=>by
    obtain⟨⟨⟨x,x'⟩,xxx⟩,xxx_mem,⟨⟨_,_⟩,_⟩,xxxx_mem,rfl,rfl,rfl,rfl⟩:=law3 _ h rfl
    exact⟨_,⟨_,xxx_mem,xxxx_mem⟩⟩
   law4:=fun h eq=>by
    obtain⟨⟨⟨_,_⟩,_⟩,xx_mem,rfl,h⟩:=law4 _ h (by simp [eq])
    simp only at eq h
    rw [←eq]
    exact⟨_,eq.symm▸(h▸xx_mem)⟩}
theorem ev {e: Ext ℕ} {S: List ((Nat×ₗNat)×Nat)} (hS: e.1=fl S)
  (a b c: Nat) (h: (toLex (a,b),c)∈S:=by decide):
  haveI: Magma Nat:=instMagma e; a◇ b=c:=(Ext.base e (hS▸ h)).symm
end
end Greedy
open Greedy PartialMagma
def seed: List ((Nat×ₗNat)×Nat):=[((0,0),1),((0,1),2),((1,0),2),((1,1),3),((1,2),0),((1,3),1),((1,4),2),((2,0),3),((2,1),4),((3,0),4),((3,1),1),((3,3),3),((3,4),0)]
noncomputable def e: Ext Nat:=⟨fl seed,flOK⟩
abbrev G:=GM e
noncomputable instance: Magma G:=instMagma e
theorem source: EquationLHS G:=e.eq1722
theorem counter: ¬ EquationRHS G:=by
 intro h
 have t:=h 0 0
 rw [show ((0:G)◇0)=1 from ev rfl 0 0 1,show ((1:G)◇0)=2 from ev rfl 1 0 2,show ((2:G)◇0)=3 from ev rfl 2 0 3,show ((3:G)◇0)=4 from ev rfl 3 0 4] at t
 have u:(0:Nat)=4:=t
 omega
end EQ
end submission
def submission:Goal:=⟨submission.EQ.G,submission.EQ.instMagmaG,submission.EQ.source,submission.EQ.counter⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1722_to_3143 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1722_to_3143
