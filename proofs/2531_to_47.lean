-- Equation2531 → Equation47
-- Recorded verdict: false
-- Premise: x = (y ◇ ((y ◇ x) ◇ x)) ◇ y
-- Conclusion: x = x ◇ (x ◇ (x ◇ x))
-- Original submission SHA-256: 9a2623d2d76f20d280245619bb21e792d708e10c01b08f484fbf9067ea9220c2
-- Aurora-accepted correction SHA-256: c3fae2aa29a766daa87eed5d18e5ca0f471cb66e0be606ba135944a0b1c58982
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ ((y ◇ x) ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ (x ◇ (x ◇ x))
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
namespace Q
abbrev OldLaw (G:Type) [Magma G]:=∀ x y:G,x=y◇((x◇(x◇y))◇y)
namespace Greedy
noncomputable section
open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : P α) : Prop where
  eq1076 {x y xy xxy} : xy ∈ E x y → xxy ∈ E x xy → ∃xxyy, xxyy ∈ E xxy y ∧ x ∈ E y xxyy
  not_idempotent {x} : x ∉ E x x

def leq {α β : Type} (e : α ≃ β) (E : P β) (ok : Laws E) :
  Laws (Equiv.mv e E) where
  eq1076 xy_mem xxy_mem := by
    obtain ⟨xxyy, xxyy_mem, eq⟩ := ok.eq1076 xy_mem xxy_mem
    exact ⟨e.symm xxyy, by simpa using xxyy_mem, by simpa using eq⟩
  not_idempotent h := by simpa using ok.not_idempotent (by simpa using h)

scoped instance : R where
  laws := Laws
  laws_equiv := leq

class C1 extends B where

namespace C1
variable [C1]
open B

private abbrev F := Unit ⊕ Fin db ⊕ Fin db

open B

inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ E x y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr $ .inl ())
  | extra1 {d} (h : b ∈ E a d) :
    Next (.inr $ .inl ()) (.inl d) (.inr $ .inr $ .inl ⟨d, ldb $ dr h⟩)
  | extra2 {d} (h : b ∈ E a d) :
    Next (.inl d) (.inr $ .inr $ .inl ⟨d, ldb $ dr h⟩) (.inl a)
  | extra3_1 {d e} (h : b ∈ E a d) : d ≠ e → e ∈ E d a →
    Next (.inr $ .inr $ .inl ⟨d, ldb $ dr h⟩)
      (.inr $ .inr $ .inr ⟨d, ldb $ dr h⟩) (.inl d)
  | extra3_2 {d e} (h : b ∈ E a d) : d ≠ e → e ∈ E d a →
    Next (.inl e) (.inr $ .inr $ .inl ⟨d, ldb $ dr h⟩)
      (.inr $ .inr $ .inr ⟨d, ldb $ dr h⟩)
  | extra4_1 {d} (h : b ∈ E a d) : d ∈ E d a →
    Next (.inr $ .inr $ .inl ⟨d, ldb $ dr h⟩) (.inl a) (.inl d)
  | extra4_2 {d} (h : b ∈ E a d) : d ∈ E d a →
    Next (.inl d) (.inr $ .inr $ .inl ⟨d, ldb $ dr h⟩) (.inl a)

abbrev n : P (ℕ ⊕ F) := fun a b => {c | Next a b c}

theorem nf : ∀ {x y}, Set.Subsingleton (n x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem <;>
  cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  all_goals try tauto
  all_goals exfalso ; apply ndf ; assumption

theorem nni {x y} : x = y → x ∉ n x y := by
  intro eq x_mem
  cases x_mem
  case base h =>
    simp only [Sum.inl.injEq] at eq
    rw [eq] at h
    apply ok.laws.not_idempotent h
  case extra4_2 h =>
    apply ok.laws.not_idempotent h
  case extra2 => injection eq

theorem neq {x y xy xxy} : xy ∈ n x y → xxy ∈ n x xy → ∃xxyy, xxyy ∈ n xxy y ∧ x ∈ n y xxyy := by
  intro xy_mem xxy_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases xxy_mem
  case base.base xy_mem _ xxy_mem =>
    obtain ⟨xxyy, xxyy_mem, eq⟩ := ok.laws.eq1076 xy_mem xxy_mem
    exact ⟨.inl xxyy, .base xxyy_mem, .base eq⟩
  case base.new h =>
    exact ⟨_, .extra1 h, .extra2 h⟩
  case extra2.base d h e h' =>
    rw [← ha , ← hb] at *
    by_cases eq : d = e
    · exact ⟨_, eq ▸ .extra2 h, .extra4_1 h (eq ▸ h')⟩
    · exact ⟨_, .extra3_2 h eq h', .extra3_1 h eq h'⟩
  case extra2.new h =>
    rw [ha, hb] at h
    exact (ok.laws.not_idempotent h).elim
  case extra3_1.extra4_1 h => exact (ok.laws.not_idempotent h).elim
  case extra4_1.extra4_1 h => exact (ok.laws.not_idempotent h).elim
  case extra4_2.new h _ => exact (ndf h).elim
  case extra4_2.base d d_mem h e h' =>
    have eq : d = e := ok.func d_mem h'
    rw [←ha, ←hb ] at *
    exact ⟨_, eq ▸ .extra2 h, .extra4_1 h (eq ▸ h')⟩

def df : Finset (ℕ ⊕F )  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem nok : n.OK where
  finite := by
    apply Set.Finite.subset (s := SetLike.coe ((df ×ˢ df) ×ˢ df)) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold df
    simp at hx ⊢; cases hx with
    | base h => simp [dout h, dl h, dr h]
    | new => simp [da, dbb]
    | extra1 h => simp [dr h]
    | extra3_2 h _ h' => simp [dout h']
    | _ h => simp [da, dr h]
  func {x y xy} hxy {xy'} hxy' := nf hxy hxy'
  laws := {
  not_idempotent := nni rfl
  eq1076 := neq
  }
def ns : Sol F Next where
  base := Next.base
  ok := nok
  ab_def := ⟨_, Next.new⟩

end C1
open B

theorem lift : ∀ (E : Ext ℕ) (a b : ℕ),
  ∃ E' : Ext ℕ, E ≤ E' ∧ E' ∈ {e : Ext ℕ | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  let E1 : C1 :=
    { E, ok, a, b, ndf := (fun h' => h ⟨_, h'⟩)}
  let FE : FE _ := ⟨_, E1.ns⟩
  obtain ⟨⟨x,hx⟩⟩ := (@B.FE.aab _ E1.toB _ _ FE)
  exact ⟨⟨FE.j,FE.ao⟩,FE.al,⟨x,hx⟩⟩

variable (e₀ : Ext ℕ)

theorem total :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op (op x (op x y)) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      apply lift
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(x, y), (x, op x y), (op x (op x y), y), (y, op (op x (op x y)) y)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a (ha : a ∈ S) := Finset.forall_mem_image.1 le ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xy, xxy, xxyy, final⟩ := le
    obtain ⟨xxyy', xxyy'_def, eq⟩ := (e.2.laws.eq1076 xy xxy)
    exact e.2.func eq ((e.2.func xxyy xxyy'_def) ▸ final)
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GM (_ : Ext ℕ) := ℕ

instance (n) : OfNat (GM e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GM e₀) where
  op := (total e₀).choose

theorem _root_.submission.PartialMagma.Ext.eq1076 : OldLaw (GM e₀) :=
  (total e₀).choose_spec.1

theorem Ext.base : ∀ {x y z : GM e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (total e₀).choose_spec.2

def fl (S : List ((Nat × Nat) × Nat)) : P ℕ := fun a b => {c | ((a, b), c) ∈ S}

theorem flOK {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.IsChain (fun a b => a.1 < b.1) := by decide)
    (eq1076 : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a.2 = b.1.2 →
      ∃ c ∈ S, ∃ d ∈ S, c.1.1 = b.2 ∧ c.1.2 = a.1.2 ∧ d.1.2 = c.2 ∧ d.1.1 = a.1.2 ∧ d.2 = a.1.1 := by decide)
    (not_idempotent : ∀ a ∈ S, a.1.1 = a.1.2 → a.2 ≠ a.1.1 := by decide) :
    (fl S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    letI : Std.Symm (fun a b : ((ℕ ×ₗ ℕ) × ℕ) => a.1 ≠ b.1) :=
      ⟨fun _ _ h => h.symm⟩
    (List.isChain_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  laws := {
  eq1076 := fun h1 h2 => by 
    obtain ⟨⟨⟨y, y'⟩,yy⟩, yy_mem, ⟨⟨yy', xyy⟩,x⟩, eq_mem, y_def,
    y'_def, yy'_def, xyy_def, x_def⟩ := eq1076 _ h1 _ h2 rfl rfl
    simp only at yy_mem eq_mem y_def y'_def yy_mem yy'_def xyy_def x_def
    exists yy
    rewrite [y_def, y'_def] at yy_mem
    use yy_mem
    use yy'_def ▸xyy_def ▸ x_def ▸ eq_mem
  not_idempotent := fun h => not_idempotent _ h rfl rfl
  }

theorem ev {e : Ext ℕ} {S : List ((Nat ×ₗ Nat) × Nat)} (hS : e.1 = fl S)
    (a b c : Nat) (h : (toLex (a, b), c) ∈ S := by decide) :
    haveI : Magma Nat := instMagma e; a ◇ b = c :=
  (Ext.base e (hS ▸ h)).symm

theorem ev' {e : Ext ℕ} {S : List ((Nat ×ₗ Nat) × Nat)} (hS : e.1 = fl S)
    (s) (h : s ∈ S) :
    haveI : Magma Nat := instMagma e; s.1.1 ◇ s.1.2 = s.2 :=
  (Ext.base e (hS ▸ h)).symm

end
end Greedy
open Greedy PartialMagma
open Greedy PartialMagma
def seed:List ((Nat×ₗNat)×Nat):=[((0,0),1),((0,2),1),((1,0),2),((2,0),2)]
noncomputable def e:Ext Nat:=⟨fl seed,flOK⟩
abbrev H:=GM e
noncomputable def D:=H
noncomputable instance (n):OfNat D n:=inferInstanceAs (OfNat H n)
noncomputable instance instD:Magma D where op x y:=@Magma.op H (instMagma e) y x
theorem source:EquationLHS D:=by
 intro x y
 change x=@Magma.op H (instMagma e) y (@Magma.op H (instMagma e) (@Magma.op H (instMagma e) x (@Magma.op H (instMagma e) x y)) y)
 exact e.eq1076 (x:=x) (y:=y)
theorem counter:¬EquationRHS D:=by
 intro h
 have t:=h (0:D)
 change (0:H)=@Magma.op H (instMagma e) (@Magma.op H (instMagma e) (@Magma.op H (instMagma e) 0 0) 0) 0 at t
 rw [show @Magma.op H (instMagma e) 0 0=1 from ev rfl 0 0 1,
 show @Magma.op H (instMagma e) 1 0=2 from ev rfl 1 0 2,
 show @Magma.op H (instMagma e) 2 0=2 from ev rfl 2 0 2] at t
 have u:(0:Nat)=2:=t
 omega
end Q
end submission
def submission:Goal:=⟨submission.Q.D,submission.Q.instD,submission.Q.source,submission.Q.counter⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2531_to_47 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2531_to_47
