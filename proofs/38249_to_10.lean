-- Equation38249 → Equation10
-- Recorded verdict: false
-- Premise: x = ((y ◇ ((x ◇ x) ◇ z)) ◇ y) ◇ y
-- Conclusion: x = x ◇ (y ◇ x)
-- Original submission SHA-256: 91b002fbd742c1825617bb9d6248753589691e3f13a8dad5934c96dfd9853811
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ ((x ◇ x) ◇ z)) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ (y ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
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

def bterm (output tail : T) : T :=
  p (p output output) tail

def fterm (owner output tail : T) : T :=
  p (p owner (bterm output tail)) owner

inductive Code : T → T → T → Prop
  | base (owner output tail : T) :
      Code (fterm owner output tail) owner output
  | hit {owner output tail hitValue : T}
      (h : Code owner (bterm output tail) hitValue) :
      Code (p hitValue owner) owner output

theorem code_right_owned {first second output : T}
    (h : Code first second output) :
    ∃ left, first = p left second := by
  cases h with
  | base owner output tail =>
      exact ⟨p _ (bterm output tail), rfl⟩
  | @hit owner output tail hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ tail, first = fterm second output tail) ∨
    (∃ tail hitValue,
      first = p hitValue second ∧
      Code second (bterm output tail) hitValue) := by
  cases h with
  | base owner output tail =>
      exact Or.inl ⟨tail, rfl⟩
  | @hit owner output tail hitValue h =>
      exact Or.inr ⟨tail, hitValue, rfl, h⟩

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz first := by
  cases h with
  | base owner output tail =>
      simp [fterm, bterm, sz] <;> omega
  | @hit owner output tail hitValue h =>
      rcases code_right_owned h with ⟨left, hshape⟩
      have hsize := congrArg sz hshape
      simp [bterm, sz] at hsize ⊢
      omega

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with
      ⟨tail₁, hbase₁⟩ |
      ⟨tail₁, hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with
        ⟨tail₂, hbase₂⟩ |
        ⟨tail₂, hitValue₂, hhit₂, hrec₂⟩
    · have houter :
          fterm second output₁ tail₁ =
            fterm second output₂ tail₂ :=
        hbase₁.symm.trans hbase₂
      have hmiddle :
          bterm output₁ tail₁ =
            bterm output₂ tail₂ :=
        (p.inj (p.inj houter).1).2
      have hsquare :
          p output₁ output₁ =
            p output₂ output₂ :=
        (p.inj hmiddle).1
      exact (p.inj hsquare).1
    · have hhitValue :
          p second (bterm output₁ tail₁) =
            hitValue₂ :=
        (p.inj (hbase₁.symm.trans hhit₂)).1
      have hsmall := code_output_small hrec₂
      rw [← hhitValue] at hsmall
      simp [sz] at hsmall <;> omega
  · rcases code_cases h₂ with
        ⟨tail₂, hbase₂⟩ |
        ⟨tail₂, hitValue₂, hhit₂, hrec₂⟩
    · have hhitValue :
          hitValue₁ =
            p second (bterm output₂ tail₂) :=
        (p.inj (hhit₁.symm.trans hbase₂)).1
      have hsmall := code_output_small hrec₁
      rw [hhitValue] at hsmall
      simp [sz] at hsmall <;> omega
    · have hhitValue : hitValue₁ = hitValue₂ :=
        (p.inj (hhit₁.symm.trans hhit₂)).1
      subst hitValue₂
      rcases code_right_owned hrec₁ with
        ⟨left₁, hright₁⟩
      rcases code_right_owned hrec₂ with
        ⟨left₂, hright₂⟩
      have hencoded :
          bterm output₁ tail₁ =
            bterm output₂ tail₂ :=
        (p.inj (hright₁.symm.trans hright₂)).2
      have hsquare :
          p output₁ output₁ =
            p output₂ output₂ :=
        (p.inj hencoded).1
      exact (p.inj hsquare).1

def baseDecode (owner left : T) :
    Option {output // Code (p left owner) owner output} :=
  match left with
  | p owner' (p (p output output') tail) =>
      if h1 : owner' = owner then
        if h2 : output' = output then by
          subst owner'; subst output'
          exact some ⟨output, Code.base owner output tail⟩
        else none
      else none
  | _ => none

def decode : (first second : T) → Option {output // Code first second output}
  | p left second', second =>
      if hs : second' = second then by
        subst second'
        exact match baseDecode second left with
        | some base => some base
        | none =>
            match hsecond : second with
            | p nestedLeft (p (p candidate candidate') nestedTail) =>
                if hc : candidate' = candidate then by
                  subst candidate'
                  exact match decode second (bterm candidate nestedTail) with
                  | some nested =>
                      if hv : nested.1 = left then by
                        subst left
                        exact some ⟨candidate, by
                          simpa [hsecond, bterm] using
                            (Code.hit (owner := second) nested.2)⟩
                      else none
                  | none => none
                else none
            | _ => none
      else none
  | _, _ => none
termination_by first _ => sz first
decreasing_by simp_all [bterm, sz] <;> omega

theorem decode_complete {first second output : T} (h : Code first second output) :
    ∃ c, decode first second = some c ∧ c.1 = output := by
  induction h with
  | base owner output tail =>
      refine ⟨⟨output, Code.base owner output tail⟩, ?_, rfl⟩
      cases owner with
      | g n => simp [decode, baseDecode, fterm, bterm]
      | p a rest =>
          cases rest with
          | g n => simp [decode, baseDecode, fterm, bterm]
          | p square tail' =>
              cases square <;> simp [decode, baseDecode, fterm, bterm]
  | @hit owner output tail hitValue h ih =>
      cases hb : baseDecode owner hitValue with
      | some base =>
          refine ⟨base, ?_, code_output_unique base.2 (Code.hit h)⟩
          cases owner with
          | g n => simp [decode, hb, bterm]
          | p a rest =>
              cases rest with
              | g n => simp [decode, hb, bterm]
              | p square tail' => cases square <;> simp [decode, hb, bterm]
      | none =>
          rcases code_right_owned h with ⟨nestedLeft, howner⟩
          rcases ih with ⟨nested, hnested, hvalue⟩
          rcases nested with ⟨nestedValue, nestedProof⟩
          dsimp at hvalue
          subst nestedValue
          subst owner
          refine ⟨⟨output, Code.hit h⟩, ?_, rfl⟩
          simp only [bterm] at hb hnested ⊢
          simp [decode, hb, hnested, bterm]

def eval (first second : T) : T :=
  match decode first second with
  | some output => output.1
  | none => p first second

theorem eval_hit {first second output : T} (h : Code first second output) :
    eval first second = output := by
  obtain ⟨c, hc, hv⟩ := decode_complete h
  simp [eval, hc, hv]

theorem eval_raw {first second : T} (h : ¬ ∃ output, Code first second output) :
    eval first second = p first second := by
  cases hd : decode first second with
  | none => simp [eval, hd]
  | some c => exact (h ⟨c.1, c.2⟩).elim

theorem no_code_same (x : T) :
    ¬ ∃ output, Code x x output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hsize := congrArg sz hshape
  simp [sz] at hsize <;> omega

theorem no_code_pair_same (x : T) :
    ¬ ∃ output, Code (p x x) x output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · have hcycle :
        x = p x (bterm output tail) :=
      (p.inj hbase).1
    have hsize := congrArg sz hcycle
    simp [bterm, sz] at hsize <;> omega
  · have hhitValue : x = hitValue :=
      (p.inj hhit).1
    subst hitValue
    have hsmall := code_output_small hrec
    omega

theorem no_code_xx_z (x z : T) :
    ¬ ∃ output, Code (p x x) z output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hz : x = z := (p.inj hshape).2
  subst z
  exact no_code_pair_same x ⟨output, h⟩

theorem no_code_raw_middle (owner encoded : T) :
    ¬ ∃ output, Code (p owner encoded) owner output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hencoded : encoded = owner :=
    (p.inj hshape).2
  subst encoded
  exact no_code_pair_same owner ⟨output, h⟩

theorem no_code_after_hit
    {owner encoded hitValue : T}
    (h : Code owner encoded hitValue) :
    ¬ ∃ output, Code hitValue owner output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  rcases code_right_owned k with ⟨left, hshape⟩
  have hsize := congrArg sz hshape
  simp [sz] at hsize
  omega

theorem source_eval (x y z : T) :
    eval
      (eval
        (eval y
          (eval (eval x x) z))
        y)
      y = x := by
  rw [eval_raw (no_code_same x)]
  rw [eval_raw (no_code_xx_z x z)]
  change
    eval
      (eval
        (eval y (bterm x z))
        y)
      y = x
  by_cases hcollision :
      ∃ hitValue, Code y (bterm x z) hitValue
  · rcases hcollision with ⟨hitValue, hhit⟩
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit hhit)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_middle y (bterm x z))]
    exact eval_hit (Code.base y x z)

instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = ((y ◇ ((x ◇ x) ◇ z)) ◇ y) ◇ y := by
  change
    x =
      eval
        (eval
          (eval y
            (eval (eval x x) z))
          y)
        y
  exact (source_eval x y z).symm

def g0 : T := g 0
def t1 : T := p g0 g0
def t2 : T := p g0 t1
def t3 : T := p t2 g0
def t4 : T := p t3 g0
def t5 : T := p t4 g0

theorem no_code_first_atom (second : T) :
    ¬ ∃ output, Code g0 second output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  cases hshape

theorem no_code_t2_g :
    ¬ ∃ output, Code t2 g0 output := by
  rintro ⟨output, h⟩
  rcases code_right_owned h with ⟨left, hshape⟩
  have hbad : t1 = g0 :=
    (p.inj hshape).2
  cases hbad

theorem no_code_t3_g :
    ¬ ∃ output, Code t3 g0 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · have hleft :
        t2 = p g0 (bterm output tail) :=
      (p.inj hbase).1
    have hencoded :
        t1 = bterm output tail :=
      (p.inj hleft).2
    have hbad :
        g0 = p output output :=
      (p.inj hencoded).1
    cases hbad
  · exact no_code_first_atom (bterm output tail)
      ⟨hitValue, hrec⟩

theorem no_code_t4_g :
    ¬ ∃ output, Code t4 g0 output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨tail, hbase⟩ |
      ⟨tail, hitValue, hhit, hrec⟩
  · have hleft :
        t3 = p g0 (bterm output tail) :=
      (p.inj hbase).1
    have hbad : t2 = g0 :=
      (p.inj hleft).1
    cases hbad
  · exact no_code_first_atom (bterm output tail)
      ⟨hitValue, hrec⟩

end T

end submission

open submission

namespace submission.T

theorem d10TargetRefutation
    (target : @EquationRHS T T.instMagma) : False := by
  first
  | have bad := target T.g0 T.g0
    have d10step0 : T.eval ((T.g0 : T)) ((T.g0 : T)) = (T.p ((T.g0 : T)) ((T.g0 : T))) := by
      simp [T.instMagma, T.g0, T.eval, T.decode, T.baseDecode]
    have d10step1 : T.eval ((T.g0 : T)) ((T.p ((T.g0 : T)) ((T.g0 : T)))) = (T.p ((T.g0 : T)) ((T.p ((T.g0 : T)) ((T.g0 : T))))) := by
      simp [T.instMagma, T.g0, T.eval, T.decode, T.baseDecode]
    change (T.g0 : T) = (T.eval (T.g0 : T) (T.eval (T.g0 : T) (T.g0 : T))) at bad
    rw [d10step0, d10step1] at bad
    change (T.g0 : T) = (T.p ((T.g0 : T)) ((T.p ((T.g0 : T)) ((T.g0 : T))))) at bad
    simpa [T.instMagma, T.g0, T.eval, T.decode, T.baseDecode] using bad

end submission.T

def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    exact T.d10TargetRefutation target

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_38249_to_10 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_38249_to_10
