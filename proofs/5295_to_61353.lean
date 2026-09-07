-- Equation5295 → Equation61353
-- Recorded verdict: false
-- Premise: x = y * (z * (y * (y * (x * y))))
-- Conclusion: (x * y) * z = (x * (y * z)) * x
-- Original submission SHA-256: c22934cec9685454b4910034576c62f38840f2f7f58f4583a5f0e3eeb0f08284
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (y ◇ (y ◇ (x ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (x ◇ (y ◇ z)) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive T where
  | g : Nat → T
  | p : T → T → T
deriving DecidableEq

namespace T

def sz : T → Nat
  | g _ => 0
  | p a b => sz a + sz b + 1

def P (a b c : T) : T := p (p (p (p a b) a) a) c
def N (r q e : T) : T := p (p (p r q) q) e

inductive ST : T → T → Prop
  | left (a b : T) : ST a (p a b)
  | right (a b : T) : ST b (p a b)
  | trans {a b c : T} : ST a b → ST b c → ST a c

def ST.upL {x a : T} (h : ST x a) (b : T) : ST x (p a b) :=
  ST.trans h (ST.left a b)

theorem st_sz {a b : T} (h : ST a b) : sz a < sz b := by
  induction h with
  | left a b => simp [sz] <;> omega
  | right a b => simp [sz] <;> omega
  | trans _ _ ih₁ ih₂ => omega

/- `DW t n predecessor result` is the proof-relevant infinite completion
   ladder compressed into two constructors. -/
inductive DW : T → Nat → T → T → Type
  | base (a b c : T) : DW (P a b c) 0 a b
  | succ {q : T} {n : Nat} {a b : T} (w : DW q n a b) (e : T) :
      DW (N b q e) (n + 1) q a

structure D (t : T) where
  level : Nat
  pred : T
  out : T
  wit : DW t level pred out

def mkBase (a b c : T) : D (P a b c) :=
  ⟨0, a, b, DW.base a b c⟩

def mkSucc {q : T} (d : D q) (e : T) : D (N d.out q e) :=
  ⟨d.level + 1, q, d.pred, DW.succ d.wit e⟩

theorem dw_pred_st {t : T} {n : Nat} {a b : T}
    (w : DW t n a b) : ST a t := by
  cases w with
  | base a b c =>
      exact ST.upL (ST.right (p (p a b) a) a) c
  | succ w e =>
      exact ST.upL (ST.right _ _) e

theorem dw_out_st {t : T} {n : Nat} {a b : T}
    (w : DW t n a b) : ST b t := by
  cases w with
  | base a b c =>
      exact ST.upL (ST.upL (ST.upL (ST.right a b) a) a) c
  | succ w e =>
      exact ST.trans (dw_pred_st w)
        (ST.upL (ST.right _ _) e)

theorem D.pred_small {t : T} (d : D t) : sz d.pred < sz t :=
  st_sz (dw_pred_st d.wit)

theorem D.out_small {t : T} (d : D t) : sz d.out < sz t :=
  st_sz (dw_out_st d.wit)

theorem D.pred_left_small {a b : T} (d : D (p a b)) :
    sz d.pred < sz a := by
  cases d with
  | mk n q r w =>
      cases w with
      | base u v c => simp [P, sz] <;> omega
      | succ w e => simp [N, sz] <;> omega

theorem D.out_left_small {a b : T} (d : D (p a b)) :
    sz d.out < sz a := by
  cases d with
  | mk n q r w =>
      cases w with
      | base u v c => simp [P, sz] <;> omega
      | succ w e =>
          have hs := st_sz (dw_pred_st w)
          simp [N, sz] at * <;> omega

def baseDecode : (t : T) → Option (D t)
  | p (p (p (p a b) a') a'') c =>
      if h₁ : a = a' then
        if h₂ : a = a'' then by
          subst a'
          subst a''
          exact some (mkBase a b c)
        else none
      else none
  | _ => none

def decode : (t : T) → Option (D t)
  | g _ => none
  | p (p (p r q) q') e =>
      if hq : q = q' then by
        subst q'
        exact
          match decode q with
          | none => baseDecode (N r q e)
          | some d =>
              if ho : d.out = r then by
                subst r
                exact some (mkSucc d e)
              else baseDecode (N r q e)
      else baseDecode (p (p (p r q) q') e)
  | t => baseDecode t
termination_by t => sz t
decreasing_by simp [sz] <;> omega

theorem base_succ_exclusive
    {a b c q : T} {n : Nat} {u v e : T}
    (w : DW q n u v) (h : P a b c = N v q e) : False := by
  have hs := st_sz (dw_out_st w)
  have h₁ := p.inj h
  have h₂ := p.inj h₁.1
  have h₃ := p.inj h₂.1
  have hqa : q = a := h₂.2.symm
  have hv : v = p a b := h₃.1.symm
  rw [hqa, hv] at hs
  simp [sz] at hs <;> omega

theorem decode_P (a b c : T) :
    decode (P a b c) = some (mkBase a b c) := by
  cases hd : decode a with
  | none =>
      simp [P, N, decode, hd, baseDecode, mkBase]
  | some d =>
      have hn : d.out ≠ p a b := by
        intro h
        have hs := d.out_small
        rw [h] at hs
        simp [sz] at hs <;> omega
      simp [P, N, decode, hd, hn, baseDecode, mkBase]

theorem decode_N {q : T} (d : D q) (e : T)
    (hd : decode q = some d) :
    decode (N d.out q e) = some (mkSucc d e) := by
  simp [N, decode, hd, mkSucc]

theorem decode_double_pred_ne (a b : T)
    (d : D (p (p a b) a)) : d.pred ≠ a := by
  intro h
  have hs := congrArg sz h
  cases d with
  | mk n q r w =>
      cases w with
      | base u v c =>
          simp [P, sz] at hs <;> omega
      | succ w e =>
          simp [N, sz] at hs <;> omega

theorem decode_prefix_none (a b : T) :
    decode (p (p (p a b) a) a) = none := by
  cases hd : decode (p (p (p a b) a) a) with
  | none => rfl
  | some d =>
      exfalso
      cases d with
      | mk n q r w =>
          cases w with
          | succ w e =>
              have hs := st_sz (dw_out_st w)
              simp [N, sz] at hs <;> omega

theorem decode_collision_none_raw {o y : T} (hy : sz o < sz y) :
    decode (p (p o y) y) = none := by
  cases hd : decode (p (p o y) y) with
  | none => rfl
  | some k =>
      exfalso
      cases k with
      | mk n q r w =>
          cases w with
          | base u v c =>
              simp [P, sz] at hy <;> omega
          | succ w e =>
              simp [N, sz] at hy <;> omega

theorem decode_collision_none {y : T} (d : D y) :
    decode (p (p d.out y) y) = none :=
  decode_collision_none_raw d.out_small

def eval (a b : T) : T :=
  match decode a with
  | none => p a b
  | some d => if d.pred = b then d.out else p a b

theorem eval_none {a b : T} (h : decode a = none) :
    eval a b = p a b := by simp [eval, h]

theorem eval_hit {a b : T} (d : D a)
    (hd : decode a = some d) (h : d.pred = b) :
    eval a b = d.out := by simp [eval, hd, h]

theorem eval_miss {a b : T} (d : D a)
    (hd : decode a = some d) (h : d.pred ≠ b) :
    eval a b = p a b := by simp [eval, hd, h]

theorem eval_small_raw {a b : T} (h : sz a < sz b) :
    eval a b = p a b := by
  cases hd : decode a with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.pred_small
      rw [he] at hs
      omega

theorem eval_pair_left (a b : T) :
    eval (p a b) a = p (p a b) a := by
  cases hd : decode (p a b) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.pred_left_small
      rw [he] at hs
      omega

theorem eval_double_left (a b : T) :
    eval (p (p a b) a) a = p (p (p a b) a) a := by
  cases hd : decode (p (p a b) a) with
  | none => exact eval_none hd
  | some d => exact eval_miss d hd (decode_double_pred_ne a b d)

theorem eval_P (a b c : T) : eval (P a b c) a = b :=
  eval_hit (mkBase a b c) (decode_P a b c) rfl

theorem eval_N {q : T} (d : D q) (e : T)
    (hd : decode q = some d) :
    eval (N d.out q e) q = d.pred :=
  eval_hit (mkSucc d e) (decode_N d e hd) rfl

theorem source_raw (x y z : T) (h : eval y x = p y x) :
    eval (eval (eval (eval (eval y x) y) y) z) y = x := by
  rw [h, eval_pair_left, eval_double_left]
  rw [eval_none (decode_prefix_none y x)]
  exact eval_P y x z

theorem source_collision {x y : T} (d : D y) (z : T)
    (hd : decode y = some d) (hx : d.pred = x) :
    eval (eval (eval (eval (eval y x) y) y) z) y = x := by
  have hs := d.out_small
  rw [eval_hit d hd hx]
  rw [eval_small_raw hs]
  have h₂ :
      eval (p d.out y) y = p (p d.out y) y := by
    cases hk : decode (p d.out y) with
    | none => exact eval_none hk
    | some k =>
        apply eval_miss k hk
        intro he
        have hklt := k.pred_left_small
        rw [he] at hklt
        omega
  rw [h₂]
  rw [eval_none (decode_collision_none d)]
  change eval (N d.out y z) y = x
  exact (eval_N d z hd).trans hx

theorem source_holds (x y z : T) :
    x = eval (eval (eval (eval (eval y x) y) y) z) y := by
  symm
  cases hd : decode y with
  | none =>
      exact source_raw x y z (eval_none hd)
  | some d =>
      by_cases hx : d.pred = x
      · exact source_collision d z hd hx
      · exact source_raw x y z (eval_miss d hd hx)

def NoRedex (a b : T) : Prop :=
  match decode a with
  | none => True
  | some d => d.pred ≠ b

def NF : T → Prop
  | g _ => True
  | p a b => NF a ∧ NF b ∧ NoRedex a b

theorem nf_st {a b : T} (h : ST a b) (hb : NF b) : NF a := by
  induction h with
  | left a b => exact hb.1
  | right a b => exact hb.2.1
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hb)

theorem eval_nf {a b : T} (ha : NF a) (hb : NF b) :
    NF (eval a b) := by
  cases hd : decode a with
  | none =>
      rw [eval_none hd]
      exact ⟨ha, hb, by simp [NoRedex, hd]⟩
  | some d =>
      by_cases hp : d.pred = b
      · rw [eval_hit d hd hp]
        exact nf_st (dw_out_st d.wit) ha
      · rw [eval_miss d hd hp]
        exact ⟨ha, hb, by simp [NoRedex, hd, hp]⟩

instance instMagma : Magma T where
  op := eval

def gx : T := g 0
def gy : T := g 1
def gz : T := g 2
def gw : T := g 3

theorem bad35265 :
    gx ≠ eval (eval (eval gy gz) (eval (eval gw gx) gw)) gy := by
  intro h
  simp [gx, gy, gz, gw, eval, decode, baseDecode] at h

theorem bad12142 :
    gx ≠ eval gy (eval (eval (eval gy gz) gx) (eval gx gw)) := by
  intro h
  simp [gx, gy, gz, gw, eval, decode, baseDecode] at h

theorem bad6540 :
    gx ≠ eval gx (eval gy (eval (eval gy gx) (eval gx gz))) := by
  intro h
  simp [gx, gy, gz, gw, eval, decode, baseDecode] at h

end T
end submission


namespace submission
namespace T

def oppositeMagma : Magma T where
  op a b := eval b a

theorem bad61353_opposite :
    eval gz (eval gy gx) ≠
      eval gx (eval (eval gz gy) gx) := by
  intro h
  simp [gx, gy, gz, eval, decode, baseDecode] at h

end T
end submission

open submission

def submission : Goal := by
  refine ⟨T, T.oppositeMagma, ?_, ?_⟩
  · intro x y z
    change x =
      T.eval (T.eval (T.eval (T.eval (T.eval y x) y) y) z) y
    exact T.source_holds x y z
  · intro target
    exact T.bad61353_opposite (target T.gx T.gy T.gz)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5295_to_61353 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5295_to_61353
