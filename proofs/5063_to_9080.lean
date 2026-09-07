-- Equation5063 → Equation9080
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ (x ◇ (y ◇ (y ◇ y))))
-- Conclusion: x = x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))
-- Original submission SHA-256: 2fe1e878c32dd9b01a80b02b153ebc94ac57d5bc923cea4decb1471edbfeec88
-- Aurora-accepted correction SHA-256: 7d78c7b11f454aadb3932c947179677c6f0ee089b7fdd068e607fdaa9dc86de0
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ (x ◇ (y ◇ (y ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
-- stage:stage0_generalized_infinite_source_family
                   

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

def gx : T := g 0
def gy : T := g 1
def gz : T := g 2
def gw : T := g 3

namespace D39

def P (a b c : T) : T := p (p (p (p a b) a) c) a
def N (r q e : T) : T := p (p (p r q) e) q

inductive DW : T → Nat → T → T → Type
  | base (a b c : T) : DW (P a b c) 0 a c
  | succ {q : T} {n : Nat} {a b : T} (w : DW q n a b) (e : T) :
      DW (N b q e) (n + 1) q e

structure D (t : T) where
  level : Nat
  key : T
  value : T
  wit : DW t level key value

def mkBase (a b c : T) : D (P a b c) :=
  ⟨0, a, c, DW.base a b c⟩

def mkSucc {q : T} (d : D q) (e : T) : D (N d.value q e) :=
  ⟨d.level + 1, q, e, DW.succ d.wit e⟩

theorem dw_key_st {t : T} {n : Nat} {a b : T}
    (w : DW t n a b) : ST a t := by
  cases w with
  | base a b c => exact ST.right _ _
  | succ w e => exact ST.right _ _

theorem dw_value_st {t : T} {n : Nat} {a b : T}
    (w : DW t n a b) : ST b t := by
  cases w with
  | base a b c =>
      exact ST.upL (ST.right _ _) _
  | succ w e =>
      exact ST.upL (ST.right _ _) _

theorem D.key_small {t : T} (d : D t) : sz d.key < sz t :=
  st_sz (dw_key_st d.wit)

theorem D.value_small {t : T} (d : D t) : sz d.value < sz t :=
  st_sz (dw_value_st d.wit)

theorem D.key_root {a b : T} (d : D (p a b)) : d.key = b := by
  cases d with
  | mk n k v w => cases w <;> rfl

theorem D.key_left_small {a b : T} (d : D (p a b)) :
    sz d.key < sz a := by
  cases d with
  | mk n k v w =>
      cases w with
      | base u v c => simp [P, sz] <;> omega
      | succ w e => simp [N, sz] <;> omega

theorem D.key_left_left_small {a b c : T} (d : D (p (p a b) c)) :
    sz d.key < sz a := by
  cases d with
  | mk n k v w =>
      cases w with
      | base u v c => simp [P, sz] <;> omega
      | succ w e => simp [N, sz] <;> omega

theorem D.key_spine {a b c e : T} (d : D (p (p (p a b) c) e)) :
    d.key = b := by
  cases d with
  | mk n k v w => cases w <;> rfl

theorem D.spine_ne {a b c e : T} (d : D (p (p (p a b) c) e)) :
    a ≠ b := by
  intro h
  have hs := congrArg sz h
  cases d with
  | mk n k v w =>
      cases w with
      | base u v c => simp [P, sz] at hs <;> omega
      | succ w e =>
          have hw := st_sz (dw_value_st w)
          omega

def baseDecode : (t : T) → Option (D t)
  | p (p (p (p a b) a') c) a'' =>
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
  | p (p (p r q) e) q' =>
      if hq : q = q' then by
        subst q'
        exact
          match decode q with
          | none => baseDecode (N r q e)
          | some d =>
              if hv : d.value = r then by
                subst r
                exact some (mkSucc d e)
              else baseDecode (N r q e)
      else baseDecode (p (p (p r q) e) q')
  | t => baseDecode t
termination_by t => sz t
decreasing_by simp [sz] <;> omega

theorem base_succ_exclusive
    {a b c q : T} {n : Nat} {u v e : T}
    (w : DW q n u v) (h : P a b c = N v q e) : False := by
  have hs := st_sz (dw_value_st w)
  have h₁ := p.inj h
  have h₂ := p.inj h₁.1
  have h₃ := p.inj h₂.1
  have hqa : q = a := h₁.2.symm
  have hv : v = p a b := h₃.1.symm
  rw [hqa, hv] at hs
  simp [sz] at hs <;> omega

theorem decode_P (a b c : T) :
    decode (P a b c) = some (mkBase a b c) := by
  cases hd : decode a with
  | none => simp [P, N, decode, hd, baseDecode, mkBase]
  | some d =>
      have hn : d.value ≠ p a b := by
        intro h
        have hs := d.value_small
        rw [h] at hs
        simp [sz] at hs <;> omega
      simp [P, N, decode, hd, hn, baseDecode, mkBase]

theorem decode_N {q : T} (d : D q) (e : T)
    (hd : decode q = some d) :
    decode (N d.value q e) = some (mkSucc d e) := by
  simp [N, decode, hd, mkSucc]

theorem decode_double_none (a b : T) :
    decode (p (p a b) a) = none := by
  cases hd : decode (p (p a b) a) with
  | none => rfl
  | some d =>
      exfalso
      have hk := d.key_root
      have hs := d.key_left_left_small
      rw [hk] at hs
      omega

theorem decode_pair_none_lt {a b : T} (h : sz a < sz b) :
    decode (p a b) = none := by
  cases hd : decode (p a b) with
  | none => rfl
  | some d =>
      exfalso
      have hk := d.key_root
      have hs := d.key_left_small
      rw [hk] at hs
      omega

def eval (a b : T) : T :=
  match decode a with
  | none => p a b
  | some d => if d.key = b then d.value else p a b

theorem eval_none {a b : T} (h : decode a = none) :
    eval a b = p a b := by simp [eval, h]

theorem eval_hit {a b : T} (d : D a)
    (hd : decode a = some d) (h : d.key = b) :
    eval a b = d.value := by simp [eval, hd, h]

theorem eval_miss {a b : T} (d : D a)
    (hd : decode a = some d) (h : d.key ≠ b) :
    eval a b = p a b := by simp [eval, hd, h]

theorem eval_small_raw {a b : T} (h : sz a < sz b) :
    eval a b = p a b := by
  cases hd : decode a with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_small
      rw [he] at hs
      omega

theorem eval_pair_left (a b : T) :
    eval (p a b) a = p (p a b) a := by
  cases hd : decode (p a b) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_left_small
      rw [he] at hs
      omega

theorem eval_triple_left (a b c : T) :
    eval (p (p (p a b) a) c) a = p (p (p (p a b) a) c) a := by
  cases hd : decode (p (p (p a b) a) c) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hb : d.key = b := d.key_spine
      exact d.spine_ne (he.symm.trans hb)

theorem eval_collision_third {r y : T} (h : sz r < sz y) (x : T) :
    eval (p (p r y) x) y = p (p (p r y) x) y := by
  cases hd : decode (p (p r y) x) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_left_left_small
      rw [he] at hs
      omega

theorem eval_P (a b c : T) : eval (P a b c) a = c :=
  eval_hit (mkBase a b c) (decode_P a b c) rfl

theorem eval_N {q : T} (d : D q) (e : T)
    (hd : decode q = some d) :
    eval (N d.value q e) q = e :=
  eval_hit (mkSucc d e) (decode_N d e hd) rfl

theorem source_raw (x y z : T) (h : eval y z = p y z) :
    eval (eval (eval (eval (eval y z) y) x) y) y = x := by
  rw [h, eval_pair_left]
  rw [eval_none (decode_double_none y z)]
  rw [eval_triple_left]
  exact eval_P y z x

theorem source_collision {y : T} (d : D y) (x z : T)
    (hd : decode y = some d) (hz : d.key = z) :
    eval (eval (eval (eval (eval y z) y) x) y) y = x := by
  have hs := d.value_small
  rw [eval_hit d hd hz]
  rw [eval_small_raw hs]
  rw [eval_none (decode_pair_none_lt hs)]
  rw [eval_collision_third hs]
  change eval (N d.value y x) y = x
  exact eval_N d x hd

theorem source_holds (x y z : T) :
    x = eval (eval (eval (eval (eval y z) y) x) y) y := by
  symm
  cases hd : decode y with
  | none => exact source_raw x y z (eval_none hd)
  | some d =>
      by_cases hz : d.key = z
      · exact source_collision d x z hd hz
      · exact source_raw x y z (eval_miss d hd hz)

def magma : Magma T where
  op := eval

end D39

namespace D53

def P (a b c : T) : T := p (p (p (p a b) a) a) c
def N (r q e : T) : T := p (p (p r q) q) e

inductive DW : T → Nat → T → T → Type
  | base (a b c : T) : DW (P a b c) 0 b c
  | succ {q : T} {n : Nat} {a b : T} (w : DW q n a b) (e : T) :
      DW (N b q e) (n + 1) a e

structure D (t : T) where
  level : Nat
  key : T
  value : T
  wit : DW t level key value

def mkBase (a b c : T) : D (P a b c) :=
  ⟨0, b, c, DW.base a b c⟩

def mkSucc {q : T} (d : D q) (e : T) : D (N d.value q e) :=
  ⟨d.level + 1, d.key, e, DW.succ d.wit e⟩

theorem dw_key_st {t : T} {n : Nat} {a b : T}
    (w : DW t n a b) : ST a t := by
  induction w with
  | base a b c =>
      exact ST.upL (ST.upL (ST.upL (ST.right _ _) _) _) _
  | succ w e ih =>
      exact ST.trans ih
        (ST.upL (ST.right _ _) _)

theorem dw_value_st {t : T} {n : Nat} {a b : T}
    (w : DW t n a b) : ST b t := by
  cases w with
  | base a b c => exact ST.right _ _
  | succ w e => exact ST.right _ _

theorem D.key_small {t : T} (d : D t) : sz d.key < sz t :=
  st_sz (dw_key_st d.wit)

theorem D.value_small {t : T} (d : D t) : sz d.value < sz t :=
  st_sz (dw_value_st d.wit)

theorem D.key_left_small {a b : T} (d : D (p a b)) :
    sz d.key < sz a := by
  cases d with
  | mk n k v w =>
      cases w with
      | base u v c => simp [P, sz] <;> omega
      | succ w e =>
          have hs := st_sz (dw_key_st w)
          simp [N, sz] at * <;> omega

theorem D.key_left_left_small {a b c : T} (d : D (p (p a b) c)) :
    sz d.key < sz a := by
  cases d with
  | mk n k v w =>
      cases w with
      | base u v c => simp [P, sz] <;> omega
      | succ w e =>
          have hs := st_sz (dw_key_st w)
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
              if hv : d.value = r then by
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
  have hs := st_sz (dw_value_st w)
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
  | none => simp [P, N, decode, hd, baseDecode, mkBase]
  | some d =>
      have hn : d.value ≠ p a b := by
        intro h
        have hs := d.value_small
        rw [h] at hs
        simp [sz] at hs <;> omega
      simp [P, N, decode, hd, hn, baseDecode, mkBase]

theorem decode_N {q : T} (d : D q) (e : T)
    (hd : decode q = some d) :
    decode (N d.value q e) = some (mkSucc d e) := by
  simp [N, decode, hd, mkSucc]

theorem decode_prefix_none (a b : T) :
    decode (p (p (p a b) a) a) = none := by
  cases hd : decode (p (p (p a b) a) a) with
  | none => rfl
  | some d =>
      exfalso
      cases d with
      | mk n k v w =>
          cases w with
          | succ w e =>
              have hs := st_sz (dw_value_st w)
              simp [N, sz] at hs <;> omega

theorem decode_collision_none_raw {o y : T} (hy : sz o < sz y) :
    decode (p (p o y) y) = none := by
  cases hd : decode (p (p o y) y) with
  | none => rfl
  | some d =>
      exfalso
      cases d with
      | mk n k v w =>
          cases w with
          | base u v c => simp [P, sz] at hy <;> omega
          | succ w e => simp [N, sz] at hy <;> omega

def eval (a b : T) : T :=
  match decode a with
  | none => p a b
  | some d => if d.key = b then d.value else p a b

theorem eval_none {a b : T} (h : decode a = none) :
    eval a b = p a b := by simp [eval, h]

theorem eval_hit {a b : T} (d : D a)
    (hd : decode a = some d) (h : d.key = b) :
    eval a b = d.value := by simp [eval, hd, h]

theorem eval_miss {a b : T} (d : D a)
    (hd : decode a = some d) (h : d.key ≠ b) :
    eval a b = p a b := by simp [eval, hd, h]

theorem eval_small_raw {a b : T} (h : sz a < sz b) :
    eval a b = p a b := by
  cases hd : decode a with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_small
      rw [he] at hs
      omega

theorem eval_pair_left (a b : T) :
    eval (p a b) a = p (p a b) a := by
  cases hd : decode (p a b) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_left_small
      rw [he] at hs
      omega

theorem eval_double_left (a b : T) :
    eval (p (p a b) a) a = p (p (p a b) a) a := by
  cases hd : decode (p (p a b) a) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_left_left_small
      rw [he] at hs
      omega

theorem eval_collision_second {o y : T} (h : sz o < sz y) :
    eval (p o y) y = p (p o y) y := by
  cases hd : decode (p o y) with
  | none => exact eval_none hd
  | some d =>
      apply eval_miss d hd
      intro he
      have hs := d.key_left_small
      rw [he] at hs
      omega

theorem eval_P (a b c : T) : eval (P a b c) b = c :=
  eval_hit (mkBase a b c) (decode_P a b c) rfl

theorem eval_N {q : T} (d : D q) (e : T)
    (hd : decode q = some d) :
    eval (N d.value q e) d.key = e :=
  eval_hit (mkSucc d e) (decode_N d e hd) rfl

theorem source_raw (x y z : T) (h : eval y z = p y z) :
    eval (eval (eval (eval (eval y z) y) y) x) z = x := by
  rw [h, eval_pair_left, eval_double_left]
  rw [eval_none (decode_prefix_none y z)]
  exact eval_P y z x

theorem source_collision {y : T} (d : D y) (x z : T)
    (hd : decode y = some d) (hz : d.key = z) :
    eval (eval (eval (eval (eval y z) y) y) x) z = x := by
  have hs := d.value_small
  rw [eval_hit d hd hz]
  rw [eval_small_raw hs]
  rw [eval_collision_second hs]
  rw [eval_none (decode_collision_none_raw hs)]
  change eval (N d.value y x) z = x
  rw [← hz]
  exact eval_N d x hd

theorem source_holds (x y z : T) :
    x = eval (eval (eval (eval (eval y z) y) y) x) z := by
  symm
  cases hd : decode y with
  | none => exact source_raw x y z (eval_none hd)
  | some d =>
      by_cases hz : d.key = z
      · exact source_collision d x z hd hz
      · exact source_raw x y z (eval_miss d hd hz)

def magma : Magma T where
  op := eval

end D53

end T
end submission


namespace submission
namespace T
namespace D39

def oppositeMagma : Magma T where
  op a b := eval b a

end D39
end T
end submission

open submission

namespace submission.T

def IsGenerator : T → Prop
  | .g _ => True
  | .p _ _ => False

def d10q : T := T.p T.gx T.gx
def d10r : T := T.p d10q T.gx
def d10s : T := T.p d10r d10q
def d10t : T := T.p d10s T.gx

theorem d10v1 : T.D39.eval T.gx T.gx = d10q := by
  apply T.D39.eval_none
  unfold T.gx
  unfold T.D39.decode
  try unfold T.D39.baseDecode
  rfl
theorem d10v2 : T.D39.eval d10q T.gx = d10r := by
  apply T.D39.eval_none
  unfold d10q T.gx
  unfold T.D39.decode
  try unfold T.D39.baseDecode
  rfl
theorem d10v3 : T.D39.eval d10r d10q = d10s := by
  apply T.D39.eval_none
  unfold d10r d10q T.gx
  unfold T.D39.decode
  try unfold T.D39.baseDecode
  rfl
theorem d10v4 : T.D39.eval d10s T.gx = d10t := by
  apply T.D39.eval_none
  unfold d10s d10r d10q T.gx
  unfold T.D39.decode
  try unfold T.D39.baseDecode
  rfl

theorem d10TargetRefutation
    (target : @EquationRHS T T.D39.oppositeMagma) : False := by
  have bad := target T.gx
  change
    T.gx =
      T.D39.eval
        (T.D39.eval
          (T.D39.eval (T.D39.eval T.gx T.gx) T.gx)
          (T.D39.eval T.gx T.gx))
        T.gx at bad
  rw [d10v1, d10v2, d10v3, d10v4] at bad
  exact Eq.mp (congrArg IsGenerator bad) True.intro

end submission.T

def submission : Goal := by
  refine ⟨T, T.D39.oppositeMagma, ?_, ?_⟩
  · intro _d10v0 _d10v1
    change (_d10v0) =
      T.D39.eval
        (T.D39.eval
          (T.D39.eval
            (T.D39.eval (T.D39.eval (_d10v1) (_d10v1)) (_d10v1)) (_d10v0)) (_d10v1)) (_d10v1)
    exact T.D39.source_holds (_d10v0) (_d10v1) (_d10v1)
  · intro target
    exact T.d10TargetRefutation target

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5063_to_9080 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5063_to_9080
