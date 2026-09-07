-- Equation17260 → Equation104
-- Recorded verdict: false
-- Premise: x = (y ◇ x) ◇ (z ◇ (x ◇ (z ◇ z)))
-- Conclusion: x = x ◇ ((y ◇ x) ◇ x)
-- Original submission SHA-256: dbcebdb178d92aa562967e5a00a4b5ba73862a7dccca6334a397abfcca2bacd4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (z ◇ (x ◇ (z ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ ((y ◇ x) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_generalized_infinite_source_family
                   

set_option maxRecDepth 10000

namespace submission

inductive CM where
  | e : CM
  | p : CM → CM → CM
deriving DecidableEq

namespace CM

def sz : CM → Nat
  | e => 0
  | p a b => sz a + sz b + 1

def r (x z : CM) : CM := p x (p z z)

def s (z x : CM) : CM := p z (r x z)

def lhs0 (a x z : CM) : CM := p (p a x) (s z x)

def lhs1 (a b c : CM) : CM :=
  p a (p b (p (s c a) (p b b)))

def get0a : CM → CM
  | p (p a _) _ => a
  | _ => e

def get0x : CM → CM
  | p (p _ x) _ => x
  | _ => e

def get0z : CM → CM
  | p _ (p z _) => z
  | _ => e

def get1a : CM → CM
  | p a _ => a
  | _ => e

def get1b : CM → CM
  | p _ (p b _) => b
  | _ => e

def get1c : CM → CM
  | p _ (p _ (p (p c _) _)) => c
  | _ => e

def root (t : CM) : CM :=
  let a0 := get0a t
  let x0 := get0x t
  let z0 := get0z t
  if t = lhs0 a0 x0 z0 then
    x0
  else
    let a1 := get1a t
    let b1 := get1b t
    let c1 := get1c t
    if t = lhs1 a1 b1 c1 then s c1 a1 else t

def op (a b : CM) : CM := root (p a b)

instance instMagma : Magma CM where
  op := op

theorem lhs1_ne_lhs0 (a b c d u : CM) :
    lhs1 a b c = lhs0 d u b → False := by
  intro h
  have hleft : a = p d u := (CM.p.inj h).1
  have hright :
      p b (p (s c a) (p b b)) = s b u :=
    (CM.p.inj h).2
  have htail :
      p (s c a) (p b b) = p u (p b b) :=
    (CM.p.inj hright).2
  have hu : s c a = u := (CM.p.inj htail).1
  have hself : a = p d (s c a) :=
    hleft.trans (congrArg (fun t => p d t) hu.symm)
  have hs := congrArg sz hself
  simp [s, r, sz] at hs
  omega

theorem root_lhs0 (a x z : CM) : root (lhs0 a x z) = x := by
  change
    (if lhs0 a x z = lhs0 a x z then x
      else
        if lhs0 a x z =
            lhs1
              (get1a (lhs0 a x z))
              (get1b (lhs0 a x z))
              (get1c (lhs0 a x z))
          then
            s
              (get1c (lhs0 a x z))
              (get1a (lhs0 a x z))
          else lhs0 a x z) = x
  rw [if_pos rfl]

theorem root_lhs1 (a b c : CM) :
    root (lhs1 a b c) = s c a := by
  change
    (if lhs1 a b c =
        lhs0
          (get0a (lhs1 a b c))
          (get0x (lhs1 a b c))
          b
      then get0x (lhs1 a b c)
      else if lhs1 a b c = lhs1 a b c then s c a
        else lhs1 a b c) = s c a
  rw [if_neg (lhs1_ne_lhs0 a b c _ _), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 :
      t = lhs0 (get0a t) (get0x t) (get0z t) → False)
    (h1 :
      t = lhs1 (get1a t) (get1b t) (get1c t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (a x z : CM) :
    op (p a x) (s z x) = x := by
  exact root_lhs0 a x z

theorem op_rule1 (a b c : CM) :
    op a (p b (p (s c a) (p b b))) = s c a := by
  exact root_lhs1 a b c

theorem no_yy_lhs0 (y a x z : CM) :
    p y y = lhs0 a x z → False := by
  intro h
  have hleft : y = p a x := (CM.p.inj h).1
  have hright : y = s z x := (CM.p.inj h).2
  have hboth : p a x = s z x := hleft.symm.trans hright
  have hself : x = p x (p z z) := (CM.p.inj hboth).2
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem no_yy_lhs1 (y a b c : CM) :
    p y y = lhs1 a b c → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : y = p b (p (s c a) (p b b)) :=
    (CM.p.inj h).2
  have hself : y = p b (p (s c y) (p b b)) :=
    hright.trans (
      congrArg (fun t => p b (p (s c t) (p b b))) hleft.symm)
  have hs := congrArg sz hself
  simp [s, r, sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _ _
  · exact no_yy_lhs1 y _ _ _

theorem no_r_lhs0 (x z a u v : CM) :
    r x z = lhs0 a u v → False := by
  intro h
  have hright : p z z = s v u := (CM.p.inj h).2
  have hz1 : z = v := (CM.p.inj hright).1
  have hz2 : z = p u (p v v) := (CM.p.inj hright).2
  have hself : z = p u (p z z) :=
    hz2.trans (congrArg (fun t => p u (p t t)) hz1.symm)
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem no_r_lhs1 (x z a b c : CM) :
    r x z = lhs1 a b c → False := by
  intro h
  have hright :
      p z z = p b (p (s c a) (p b b)) :=
    (CM.p.inj h).2
  have hz1 : z = b := (CM.p.inj hright).1
  have hz2 : z = p (s c a) (p b b) :=
    (CM.p.inj hright).2
  have hself : z = p (s c a) (p z z) :=
    hz2.trans (congrArg (fun t => p (s c a) (p t t)) hz1.symm)
  have hs := congrArg sz hself
  simp [s, r, sz] at hs
  omega

theorem op_r_raw (x z : CM) : op x (p z z) = r x z := by
  change root (r x z) = r x z
  apply root_eq_self
  · exact no_r_lhs0 x z _ _ _
  · exact no_r_lhs1 x z _ _ _

theorem no_s_lhs0 (z x a u v : CM) :
    s z x = lhs0 a u v → False := by
  intro h
  have hleft : z = p a u := (CM.p.inj h).1
  have hright : r x z = s v u := (CM.p.inj h).2
  have htail : p z z = p u (p v v) :=
    (CM.p.inj hright).2
  have hzu : z = u := (CM.p.inj htail).1
  have hself : z = p a z :=
    hleft.trans (congrArg (fun t => p a t) hzu.symm)
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem no_s_lhs1 (z x a b c : CM) :
    s z x = lhs1 a b c → False := by
  intro h
  have hleft : z = a := (CM.p.inj h).1
  have hright :
      r x z = p b (p (s c a) (p b b)) :=
    (CM.p.inj h).2
  have htail :
      p z z = p (s c a) (p b b) :=
    (CM.p.inj hright).2
  have hz : z = s c a := (CM.p.inj htail).1
  have hself : z = s c z :=
    hz.trans (congrArg (fun t => s c t) hleft.symm)
  have hs := congrArg sz hself
  simp [s, r, sz] at hs
  omega

theorem op_s_raw (z x : CM) : op z (r x z) = s z x := by
  change root (s z x) = s z x
  apply root_eq_self
  · exact no_s_lhs0 z x _ _ _
  · exact no_s_lhs1 z x _ _ _

theorem source_holds (x y z : CM) :
    x = op (op y x) (op z (op x (op z z))) := by
  rw [op_yy_raw, op_r_raw, op_s_raw]
  let a0 := get0a (p y x)
  let u0 := get0x (p y x)
  let b0 := get0z (p y x)
  by_cases h0 : p y x = lhs0 a0 u0 b0
  · have hx : x = s b0 u0 := (CM.p.inj h0).2
    have hinner : op y x = u0 := by
      unfold op
      change root (p y x) = u0
      unfold root
      change
        (if p y x = lhs0 a0 u0 b0 then u0
          else
            if p y x =
                lhs1 (get1a (p y x)) (get1b (p y x)) (get1c (p y x))
              then s (get1c (p y x)) (get1a (p y x))
              else p y x) = u0
      rw [if_pos h0]
    rw [hinner, hx]
    exact (op_rule1 u0 z b0).symm
  · let a1 := get1a (p y x)
    let b1 := get1b (p y x)
    let c1 := get1c (p y x)
    by_cases h1 : p y x = lhs1 a1 b1 c1
    · have hx :
          x = p b1 (p (s c1 a1) (p b1 b1)) :=
        (CM.p.inj h1).2
      have hinner : op y x = s c1 a1 := by
        unfold op
        change root (p y x) = s c1 a1
        unfold root
        change
          (if p y x = lhs0 a0 u0 b0 then u0
            else if p y x = lhs1 a1 b1 c1 then s c1 a1
              else p y x) = s c1 a1
        rw [if_neg h0, if_pos h1]
      rw [hinner, hx]
      exact (op_rule1 (s c1 a1) z b1).symm
    · have hinner : op y x = p y x := by
        unfold op
        apply root_eq_self
        · exact h0
        · exact h1
      rw [hinner]
      exact (op_rule0 y x z).symm

end CM

end submission

open submission

namespace submission.CM

theorem d10TargetRefutation
    (target : @EquationRHS CM CM.instMagma) : False := by
  first
  | have bad := target CM.e CM.e
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (CM.e : CM)) (CM.e : CM))) at bad
    exact nomatch bad

end submission.CM

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y z
    exact CM.source_holds x y z
  · intro target
    exact CM.d10TargetRefutation target

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17260_to_104 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_17260_to_104
