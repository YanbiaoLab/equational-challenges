-- Equation8883 → Equation51690
-- Recorded verdict: true
-- Premise: x = y ◇ (z ◇ (((z ◇ y) ◇ y) ◇ x))
-- Conclusion: x ◇ y = ((z ◇ x) ◇ (x ◇ z)) ◇ y
-- Original submission SHA-256: 6069fc5ae8a1ba5751f12082ed3bb9e8b0cc808f38ca702e16eb927319d7abea
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (((z ◇ y) ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ (x ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
def submission : Goal := by
 intro G _ h
 intro x y z
 have l3 : ∀ (B C D : G), B = (C◇(D◇(((D◇C)◇C)◇B))) := by
  intro B C D
  exact h B C D
 have l4 : ∀ (B C D : G), (((((B◇C)◇C)◇B)◇B)◇D) = (C◇D) := by
  intro B C D
  calc (((((B◇C)◇C)◇B)◇B)◇D)
   _ = (C◇(B◇(((B◇C)◇C)◇(((((B◇C)◇C)◇B)◇B)◇D)))) := ((l3 ((((((B◇C)◇C)◇B)◇B)◇D)) C B).symm).symm
   _ = (C◇D) := congrArg (C◇·) ((l3 D B (((B◇C)◇C))).symm)
 have l5 : ∀ (B C D : G), (B◇(((B◇C)◇C)◇(C◇D))) = D := by
  intro B C D
  calc (B◇(((B◇C)◇C)◇(C◇D)))
   _ = (B◇(((B◇C)◇C)◇(((((B◇C)◇C)◇B)◇B)◇D))) := congrArg (B◇·) (congrArg (((B◇C)◇C)◇·) ((l4 B C D).symm))
   _ = D := (l3 D B (((B◇C)◇C))).symm
 have l6 : ∀ (B C D E : G), (((((B◇C)◇C)◇D)◇D)◇(D◇E)) = (C◇(B◇E)) := by
  intro B C D E
  calc (((((B◇C)◇C)◇D)◇D)◇(D◇E))
   _ = (C◇(B◇(((B◇C)◇C)◇(((((B◇C)◇C)◇D)◇D)◇(D◇E))))) := ((l3 ((((((B◇C)◇C)◇D)◇D)◇(D◇E))) C B).symm).symm
   _ = (C◇(B◇E)) := congrArg (C◇·) (congrArg (B◇·) (l5 (((B◇C)◇C)) D E))
 have l7 : ∀ (B C D : G), (((B◇(C◇B))◇((C◇B)◇B))◇D) = ((C◇B)◇D) := by
  intro B C D
  calc (((B◇(C◇B))◇((C◇B)◇B))◇D)
   _ = (((((((C◇B)◇B)◇(C◇B))◇(C◇B))◇((C◇B)◇B))◇((C◇B)◇B))◇D) := congrArg (·◇D) (congrArg (·◇((C◇B)◇B)) ((l6 C B ((C◇B)) B).symm))
   _ = ((C◇B)◇D) := l4 (((C◇B)◇B)) ((C◇B)) D
 have l8 : ∀ (B C D : G), (((B◇C)◇C)◇(C◇(B◇D))) = D := by
  intro B C D
  calc (((B◇C)◇C)◇(C◇(B◇D)))
   _ = (((B◇C)◇C)◇(((((B◇C)◇C)◇B)◇B)◇(B◇D))) := congrArg (((B◇C)◇C)◇·) ((l4 B C ((B◇D))).symm)
   _ = D := l5 (((B◇C)◇C)) B D
 have l9 : ∀ (B C D E : G), ((((B◇(C◇D))◇D)◇(D◇(B◇(C◇D))))◇E) = (D◇E) := by
  intro B C D E
  clear h l3 l4 l5 l6
  grind
 have l10 : ∀ (B C D : G), ((((B◇C)◇C)◇B)◇((C◇B)◇(B◇D))) = D := by
  intro B C D
  calc ((((B◇C)◇C)◇B)◇((C◇B)◇(B◇D)))
   _ = ((((B◇C)◇C)◇B)◇((((((B◇C)◇C)◇B)◇B)◇B)◇(B◇D))) := congrArg ((((B◇C)◇C)◇B)◇·) (congrArg (·◇(B◇D)) ((l4 B C B).symm))
   _ = D := l5 ((((B◇C)◇C)◇B)) B D
 have l11 : ∀ (B C D : G), ((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇D) = (B◇D) := by
  intro B C D
  calc ((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇D)
   _ = ((((((B◇C)◇C)◇(C◇B))◇B)◇(B◇(((B◇C)◇C)◇(C◇B))))◇D) := congrArg (·◇D) (congrArg (((((B◇C)◇C)◇(C◇B))◇B)◇·) ((l5 B C B).symm))
   _ = (B◇D) := l9 (((B◇C)◇C)) C B D
 have l12 : ∀ (B C : G), ((B◇B)◇(B◇C)) = (B◇((B◇B)◇C)) := by
  intro B C
  calc ((B◇B)◇(B◇C))
   _ = (B◇((B◇B)◇((((B◇B)◇B)◇B)◇((B◇B)◇(B◇C))))) := ((l3 (((B◇B)◇(B◇C))) B ((B◇B))).symm).symm
   _ = (B◇((B◇B)◇C)) := congrArg (B◇·) (congrArg ((B◇B)◇·) (l10 B B C))
 have l13 : ∀ (B C D : G), (B◇(B◇((((B◇C)◇C)◇(C◇B))◇D))) = D := by
  intro B C D
  calc (B◇(B◇((((B◇C)◇C)◇(C◇B))◇D)))
   _ = ((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇(B◇((((B◇C)◇C)◇(C◇B))◇D))) := (l11 B C ((B◇((((B◇C)◇C)◇(C◇B))◇D)))).symm
   _ = D := l8 ((((B◇C)◇C)◇(C◇B))) B D
 have l14x : ∀ (A B C D E : G), ((A◇(((((B◇C)◇C)◇D)◇D)◇(D◇A)))◇((((((B◇C)◇C)◇D)◇D)◇(D◇A))◇E)) = (C◇(B◇E)) := by
  intro A B C D E
  calc ((A◇(((((B◇C)◇C)◇D)◇D)◇(D◇A)))◇((((((B◇C)◇C)◇D)◇D)◇(D◇A))◇E))
   _ = (((((B◇C)◇C)◇(((((B◇C)◇C)◇D)◇D)◇(D◇A)))◇(((((B◇C)◇C)◇D)◇D)◇(D◇A)))◇((((((B◇C)◇C)◇D)◇D)◇(D◇A))◇E)) := congrArg (·◇((((((B◇C)◇C)◇D)◇D)◇(D◇A))◇E)) (congrArg (·◇(((((B◇C)◇C)◇D)◇D)◇(D◇A))) ((l5 (((B◇C)◇C)) D A).symm))
   _ = (C◇(B◇E)) := l6 B C ((((((B◇C)◇C)◇D)◇D)◇(D◇A))) E
 have l14 : ∀ (B C D E : G), ((B◇(C◇(D◇B)))◇((C◇(D◇B))◇E)) = (C◇(D◇E)) := by
  intro B C D E
  have strict_rw_1 := (l14x B D C B E)
  rw [l6] at strict_rw_1
  exact strict_rw_1
 have l15 : ∀ (B C D : G), (B◇((B◇B)◇(C◇(((C◇B)◇B)◇D)))) = ((B◇B)◇D) := by
  intro B C D
  calc (B◇((B◇B)◇(C◇(((C◇B)◇B)◇D))))
   _ = ((B◇B)◇(B◇(C◇(((C◇B)◇B)◇D)))) := (l12 B ((C◇(((C◇B)◇B)◇D)))).symm
   _ = ((B◇B)◇D) := congrArg ((B◇B)◇·) ((l3 D B C).symm)
 have l16x : ∀ (A B C D : G), (A◇(A◇(((B◇(C◇(((C◇A)◇A)◇B)))◇((C◇(((C◇A)◇A)◇B))◇A))◇D))) = D := by
  intro A B C D
  calc (A◇(A◇(((B◇(C◇(((C◇A)◇A)◇B)))◇((C◇(((C◇A)◇A)◇B))◇A))◇D)))
   _ = (A◇(A◇((((A◇(C◇(((C◇A)◇A)◇B)))◇(C◇(((C◇A)◇A)◇B)))◇((C◇(((C◇A)◇A)◇B))◇A))◇D))) := congrArg (A◇·) (congrArg (A◇·) (congrArg (·◇D) (congrArg (·◇((C◇(((C◇A)◇A)◇B))◇A)) (congrArg (·◇(C◇(((C◇A)◇A)◇B))) (((l3 B A C).symm).symm)))))
   _ = D := l13 A ((C◇(((C◇A)◇A)◇B))) D
 have l16 : ∀ (B C D : G), (B◇(B◇((C◇(((C◇B)◇B)◇B))◇D))) = D := by
  intro B C D
  have strict_rw_2 := (l16x B B C D)
  rw [l14] at strict_rw_2
  exact strict_rw_2
 have l17 : ∀ (B C : G), (B◇(B◇((B◇B)◇(((B◇B)◇B)◇C)))) = ((B◇B)◇C) := by
  intro B C
  calc (B◇(B◇((B◇B)◇(((B◇B)◇B)◇C))))
   _ = (B◇((B◇B)◇(B◇(((B◇B)◇B)◇C)))) := congrArg (B◇·) ((l12 B ((((B◇B)◇B)◇C))).symm)
   _ = ((B◇B)◇C) := l15 B B C
 have l18 : ∀ (B C D : G), (B◇((((B◇C)◇C)◇(C◇B))◇(B◇D))) = D := by
  intro B C D
  calc (B◇((((B◇C)◇C)◇(C◇B))◇(B◇D)))
   _ = (B◇((((B◇C)◇C)◇(C◇B))◇((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇D))) := congrArg (B◇·) (congrArg ((((B◇C)◇C)◇(C◇B))◇·) ((l11 B C D).symm))
   _ = D := (l3 D B ((((B◇C)◇C)◇(C◇B)))).symm
 have l19 : ∀ (B C D : G), ((B◇(((B◇C)◇C)◇C))◇D) = (((C◇C)◇C)◇D) := by
  intro B C D
  calc ((B◇(((B◇C)◇C)◇C))◇D)
   _ = (((C◇C)◇C)◇(C◇(C◇((B◇(((B◇C)◇C)◇C))◇D)))) := (l8 C C (((B◇(((B◇C)◇C)◇C))◇D))).symm
   _ = (((C◇C)◇C)◇D) := congrArg (((C◇C)◇C)◇·) (l16 C B D)
 have l20 : ∀ (B C : G), (((B◇B)◇B)◇((B◇B)◇C)) = ((B◇B)◇(((B◇B)◇B)◇C)) := by
  intro B C
  calc (((B◇B)◇B)◇((B◇B)◇C))
   _ = (((B◇B)◇B)◇(B◇(B◇((B◇B)◇(((B◇B)◇B)◇C))))) := congrArg (((B◇B)◇B)◇·) ((l17 B C).symm)
   _ = ((B◇B)◇(((B◇B)◇B)◇C)) := l8 B B (((B◇B)◇(((B◇B)◇B)◇C)))
 have l21 : ∀ (B C : G), ((B◇B)◇(((B◇B)◇B)◇(((B◇B)◇B)◇C))) = C := by
  intro B C
  clear h l4 l5 l7 l8 l9 l10 l11 l12 l13 l14x l14 l15 l16x l16 l17
  grind
 have l22 : ∀ (B C : G), ((B◇B)◇(((B◇B)◇B)◇C)) = (B◇(B◇C)) := by
  intro B C
  grind
 have l23 : ∀ (B C : G), (B◇(B◇(B◇(B◇C)))) = ((B◇B)◇C) := by
  intro B C
  calc (B◇(B◇(B◇(B◇C))))
   _ = (B◇((B◇B)◇(((B◇B)◇B)◇(B◇C)))) := congrArg (B◇·) ((l22 B ((B◇C))).symm)
   _ = (B◇((B◇B)◇(((B◇B)◇B)◇(((((B◇B)◇B)◇B)◇B)◇C)))) := congrArg (B◇·) (congrArg ((B◇B)◇·) (congrArg (((B◇B)◇B)◇·) ((l4 B B C).symm)))
   _ = ((B◇B)◇C) := l15 B (((B◇B)◇B)) C
 have l24x : ∀ (A B C : G), (A◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇C)))) = ((((((B◇A)◇A)◇B)◇B)◇((((B◇A)◇A)◇B)◇B))◇C) := by
  intro A B C
  calc (A◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇C))))
   _ = (((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇C)))) := (l4 B A ((((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇(((((B◇A)◇A)◇B)◇B)◇C))))).symm
   _ = ((((((B◇A)◇A)◇B)◇B)◇((((B◇A)◇A)◇B)◇B))◇C) := l23 (((((B◇A)◇A)◇B)◇B)) C
 have l24 : ∀ (B C D : G), ((B◇((((C◇B)◇B)◇C)◇C))◇D) = ((B◇B)◇D) := by
  intro B C D
  have strict_rw_3 := ((l24x B C D).symm)
  rw [l4, l4, l4, l4, l23] at strict_rw_3
  exact strict_rw_3
 have l25 : ∀ (B C : G), ((B◇((B◇B)◇B))◇C) = (B◇C) := by
  intro B C
  calc ((B◇((B◇B)◇B))◇C)
   _ = (((B◇B)◇(B◇B))◇C) := congrArg (·◇C) ((l12 B B).symm)
   _ = (((B◇((((B◇B)◇B)◇B)◇B))◇(B◇B))◇C) := congrArg (·◇C) ((l24 B B ((B◇B))).symm)
   _ = (((B◇((((B◇B)◇B)◇B)◇B))◇(((((B◇B)◇B)◇B)◇B)◇B))◇C) := congrArg (·◇C) (congrArg ((B◇((((B◇B)◇B)◇B)◇B))◇·) ((l4 B B B).symm))
   _ = (((((B◇B)◇B)◇B)◇B)◇C) := ((l7 B ((((B◇B)◇B)◇B)) C).symm).symm
   _ = (B◇C) := ((l4 B B C).symm).symm
 have l26 : ∀ (B C : G), ((B◇(B◇((B◇B)◇B)))◇C) = ((B◇B)◇C) := by
  intro B C
  grind
 have l27 : ∀ (B C D : G), (((B◇C)◇C)◇(C◇((B◇B)◇D))) = (B◇(B◇(B◇D))) := by
  intro B C D
  calc (((B◇C)◇C)◇(C◇((B◇B)◇D)))
   _ = (((B◇C)◇C)◇(C◇(B◇(B◇(B◇(B◇D)))))) := congrArg (((B◇C)◇C)◇·) (congrArg (C◇·) ((l23 B D).symm))
   _ = (B◇(B◇(B◇D))) := l8 B C ((B◇(B◇(B◇D))))
 have l28 : ∀ (B C : G), ((B◇(B◇((B◇B)◇((B◇B)◇B))))◇C) = (B◇C) := by
  intro B C
  calc ((B◇(B◇((B◇B)◇((B◇B)◇B))))◇C)
   _ = ((B◇((B◇B)◇(B◇((B◇B)◇B))))◇C) := congrArg (·◇C) (congrArg (B◇·) ((l12 B (((B◇B)◇B))).symm))
   _ = ((B◇((B◇(B◇((B◇B)◇B)))◇(B◇((B◇B)◇B))))◇C) := congrArg (·◇C) (congrArg (B◇·) ((l26 B ((B◇((B◇B)◇B)))).symm))
   _ = ((B◇(((B◇((B◇B)◇B))◇(B◇((B◇B)◇B)))◇(B◇((B◇B)◇B))))◇C) := congrArg (·◇C) (congrArg (B◇·) (congrArg (·◇(B◇((B◇B)◇B))) ((l25 B ((B◇((B◇B)◇B)))).symm)))
   _ = (((B◇((B◇B)◇B))◇(((B◇((B◇B)◇B))◇(B◇((B◇B)◇B)))◇(B◇((B◇B)◇B))))◇C) := congrArg (·◇C) ((l25 B ((((B◇((B◇B)◇B))◇(B◇((B◇B)◇B)))◇(B◇((B◇B)◇B))))).symm)
   _ = ((B◇((B◇B)◇B))◇C) := ((l25 ((B◇((B◇B)◇B))) C).symm).symm
   _ = (B◇C) := ((l25 B C).symm).symm
 have l29 : ∀ (B C : G), ((B◇B)◇((B◇B)◇((B◇(B◇B))◇C))) = C := by
  intro B C
  clear h l3 l4 l5 l6 l7 l9 l10 l11 l13 l14x l14 l15 l16x l16 l18 l19 l20 l21 l22 l24x l24 l26 l28
  grind
 have l30x : ∀ (A B : G), (((A◇((A◇A)◇((A◇A)◇A)))◇(((A◇A)◇((A◇A)◇A))◇(A◇(A◇((A◇A)◇((A◇A)◇A))))))◇B) = (((A◇A)◇((A◇A)◇A))◇B) := by
  intro A B
  calc (((A◇((A◇A)◇((A◇A)◇A)))◇(((A◇A)◇((A◇A)◇A))◇(A◇(A◇((A◇A)◇((A◇A)◇A))))))◇B)
   _ = ((((A◇(A◇((A◇A)◇((A◇A)◇A))))◇((A◇A)◇((A◇A)◇A)))◇(((A◇A)◇((A◇A)◇A))◇(A◇(A◇((A◇A)◇((A◇A)◇A))))))◇B) := congrArg (·◇B) (congrArg (·◇(((A◇A)◇((A◇A)◇A))◇(A◇(A◇((A◇A)◇((A◇A)◇A)))))) ((l28 A (((A◇A)◇((A◇A)◇A)))).symm))
   _ = (((A◇A)◇((A◇A)◇A))◇B) := l9 A A (((A◇A)◇((A◇A)◇A))) B
 have l30 : ∀ (B C : G), (((B◇B)◇((B◇B)◇B))◇C) = ((B◇(B◇(B◇B)))◇C) := by
  intro B C
  have hx := l30x B C
  conv at hx =>
   lhs
   rw [l14, l12, l12, l12, l12, l23, l12, l25]
  exact hx.symm
 have l31 : ∀ (B C : G), ((B◇B)◇((B◇B)◇C)) = (B◇((B◇(B◇B))◇C)) := by
  intro B C
  calc ((B◇B)◇((B◇B)◇C))
   _ = ((B◇B)◇((B◇B)◇((B◇B)◇((B◇B)◇((B◇(B◇B))◇C))))) := congrArg ((B◇B)◇·) (congrArg ((B◇B)◇·) ((l29 B C).symm))
   _ = (((B◇B)◇(B◇B))◇((B◇(B◇B))◇C)) := l23 ((B◇B)) (((B◇(B◇B))◇C))
   _ = ((B◇((B◇B)◇B))◇((B◇(B◇B))◇C)) := congrArg (·◇((B◇(B◇B))◇C)) (((l12 B B).symm).symm)
   _ = (B◇((B◇(B◇B))◇C)) := ((l25 B (((B◇(B◇B))◇C))).symm).symm
 have l32 : ∀ (B C : G), ((B◇((B◇(B◇B))◇B))◇C) = ((B◇(B◇(B◇B)))◇C) := by
  intro B C
  calc ((B◇((B◇(B◇B))◇B))◇C)
   _ = (((B◇B)◇((B◇B)◇B))◇C) := congrArg (·◇C) ((l31 B B).symm)
   _ = ((B◇(B◇(B◇B)))◇C) := l30 B C
 have l33 : ∀ (B C : G), (((B◇B)◇B)◇((B◇B)◇C)) = (B◇(B◇C)) := by
  intro B C
  calc (((B◇B)◇B)◇((B◇B)◇C))
   _ = ((B◇B)◇(((B◇B)◇B)◇C)) := ((l20 B C).symm).symm
   _ = (B◇(B◇C)) := l22 B C
 have l34 : ∀ (B C D : G), (((B◇((((B◇C)◇C)◇B)◇B))◇(C◇B))◇D) = (C◇D) := by
  intro B C D
  calc (((B◇((((B◇C)◇C)◇B)◇B))◇(C◇B))◇D)
   _ = (((B◇((((B◇C)◇C)◇B)◇B))◇(((((B◇C)◇C)◇B)◇B)◇B))◇D) := congrArg (·◇D) (congrArg ((B◇((((B◇C)◇C)◇B)◇B))◇·) ((l4 B C B).symm))
   _ = (((((B◇C)◇C)◇B)◇B)◇D) := l7 B ((((B◇C)◇C)◇B)) D
   _ = (C◇D) := ((l4 B C D).symm).symm
 have l35 : ∀ (B C D : G), (((((B◇C)◇C)◇C)◇(B◇C))◇(B◇D)) = (C◇((C◇C)◇D)) := by
  intro B C D
  calc (((((B◇C)◇C)◇C)◇(B◇C))◇(B◇D))
   _ = ((C◇(((((B◇C)◇C)◇C)◇(B◇C))◇(B◇C)))◇((((((B◇C)◇C)◇C)◇(B◇C))◇(B◇C))◇D)) := (l14 C (((((B◇C)◇C)◇C)◇(B◇C))) B D).symm
   _ = ((C◇C)◇((((((B◇C)◇C)◇C)◇(B◇C))◇(B◇C))◇D)) := l24 C ((B◇C)) (((((((B◇C)◇C)◇C)◇(B◇C))◇(B◇C))◇D))
   _ = ((C◇C)◇(C◇D)) := congrArg ((C◇C)◇·) (l4 ((B◇C)) C D)
   _ = (C◇((C◇C)◇D)) := ((l12 C D).symm).symm
 have l36 : ∀ (B C D : G), (B◇((((B◇C)◇C)◇B)◇((C◇B)◇D))) = D := by
  intro B C D
  calc (B◇((((B◇C)◇C)◇B)◇((C◇B)◇D)))
   _ = (B◇((((B◇C)◇C)◇B)◇((((((B◇C)◇C)◇B)◇B)◇B)◇D))) := congrArg (B◇·) (congrArg ((((B◇C)◇C)◇B)◇·) (congrArg (·◇D) ((l4 B C B).symm)))
   _ = D := (l3 D B ((((B◇C)◇C)◇B))).symm
 have l37 : ∀ (B C : G), ((((B◇B)◇B)◇B)◇C) = ((B◇(B◇(B◇B)))◇C) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l9 l10 l11 l12 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l25 l26 l28 l29 l30 l31 l34 l35 l36
  grind
 have l38 : ∀ (B C D E : G), (B◇(((B◇C)◇C)◇D)) = (((C◇E)◇E)◇(E◇D)) := by
  intro B C D E
  calc (B◇(((B◇C)◇C)◇D))
   _ = (B◇(((B◇C)◇C)◇(C◇(((C◇E)◇E)◇(E◇D))))) := congrArg (B◇·) (congrArg (((B◇C)◇C)◇·) ((l5 C E D).symm))
   _ = (((C◇E)◇E)◇(E◇D)) := l5 B C ((((C◇E)◇E)◇(E◇D)))
 have l39 : ∀ (B C D : G), ((((B◇C)◇(C◇((C◇C)◇C)))◇(C◇(B◇C)))◇D) = (C◇D) := by
  intro B C D
  calc ((((B◇C)◇(C◇((C◇C)◇C)))◇(C◇(B◇C)))◇D)
   _ = ((((B◇C)◇(((((B◇C)◇C)◇C)◇(B◇C))◇(B◇C)))◇(C◇(B◇C)))◇D) := congrArg (·◇D) (congrArg (·◇(C◇(B◇C))) (congrArg ((B◇C)◇·) ((l35 B C C).symm)))
   _ = (C◇D) := l34 ((B◇C)) C D
 have l40 : ∀ (B C D : G), (((B◇(C◇B))◇(C◇B))◇D) = ((((B◇C)◇C)◇B)◇D) := by
  intro B C D
  calc (((B◇(C◇B))◇(C◇B))◇D)
   _ = ((((B◇C)◇C)◇B)◇((C◇B)◇(B◇(((B◇(C◇B))◇(C◇B))◇D)))) := (l10 B C ((((B◇(C◇B))◇(C◇B))◇D))).symm
   _ = ((((B◇C)◇C)◇B)◇D) := congrArg ((((B◇C)◇C)◇B)◇·) ((l3 D ((C◇B)) B).symm)
 have l41x : ∀ (A B : G), ((((A◇A)◇(A◇A))◇(A◇A))◇(A◇((A◇(A◇A))◇B))) = B := by
  intro A B
  calc ((((A◇A)◇(A◇A))◇(A◇A))◇(A◇((A◇(A◇A))◇B)))
   _ = ((((A◇A)◇(A◇A))◇(A◇A))◇((A◇A)◇((A◇A)◇B))) := congrArg ((((A◇A)◇(A◇A))◇(A◇A))◇·) ((l31 A B).symm)
   _ = B := l8 ((A◇A)) ((A◇A)) B
 have l41 : ∀ (B C : G), ((B◇(B◇B))◇(B◇((B◇(B◇B))◇C))) = C := by
  intro B C
  have strict_rw_4 := (l41x B C)
  rw [l12, l25] at strict_rw_4
  exact strict_rw_4
 have l42 : ∀ (B C : G), (B◇((B◇(B◇(B◇B)))◇((B◇B)◇C))) = C := by
  intro B C
  calc (B◇((B◇(B◇(B◇B)))◇((B◇B)◇C)))
   _ = (B◇((((B◇B)◇B)◇B)◇((B◇B)◇C))) := congrArg (B◇·) ((l37 B (((B◇B)◇C))).symm)
   _ = C := l36 B B C
 have l43 : ∀ (B C D : G), ((B◇B)◇(C◇(((C◇B)◇B)◇D))) = (B◇(B◇(B◇D))) := by
  intro B C D
  calc ((B◇B)◇(C◇(((C◇B)◇B)◇D)))
   _ = ((B◇B)◇(((B◇B)◇B)◇(B◇D))) := congrArg ((B◇B)◇·) (((l38 C B D B).symm).symm)
   _ = (B◇(B◇(B◇D))) := l22 B ((B◇D))
 have l44x : ∀ (A B C : G), (((A◇B)◇(B◇((B◇B)◇B)))◇((B◇(B◇(A◇B)))◇((B◇(A◇B))◇C))) = C := by
  intro A B C
  calc (((A◇B)◇(B◇((B◇B)◇B)))◇((B◇(B◇(A◇B)))◇((B◇(A◇B))◇C)))
   _ = (((A◇B)◇(B◇((B◇B)◇B)))◇(((((A◇B)◇(B◇((B◇B)◇B)))◇(B◇(A◇B)))◇(B◇(A◇B)))◇((B◇(A◇B))◇C))) := congrArg (((A◇B)◇(B◇((B◇B)◇B)))◇·) (congrArg (·◇((B◇(A◇B))◇C)) ((l39 A B ((B◇(A◇B)))).symm))
   _ = C := l5 (((A◇B)◇(B◇((B◇B)◇B)))) ((B◇(A◇B))) C
 have l44 : ∀ (B C D : G), (((B◇C)◇(C◇((C◇C)◇C)))◇(C◇(B◇D))) = D := by
  intro B C D
  have strict_rw_5 := (l44x B C D)
  rw [l14] at strict_rw_5
  exact strict_rw_5
 have l45 : ∀ (B C : G), ((B◇(B◇(B◇B)))◇(B◇C)) = ((B◇B)◇((B◇(B◇B))◇C)) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l18 l19 l20 l21 l22 l24x l24 l26
  clear l28 l29 l30 l31 l32 l33 l34 l35 l36 l38 l39 l41x l41 l42 l43 l44x l44
  grind
 have l46 : ∀ (B C : G), ((B◇(B◇B))◇(B◇C)) = (B◇((B◇(B◇B))◇C)) := by
  intro B C
  calc ((B◇(B◇B))◇(B◇C))
   _ = ((B◇(B◇B))◇(B◇((B◇(B◇B))◇(B◇((B◇(B◇B))◇C))))) := congrArg ((B◇(B◇B))◇·) (congrArg (B◇·) ((l41 B C).symm))
   _ = (B◇((B◇(B◇B))◇C)) := l41 B ((B◇((B◇(B◇B))◇C)))
 have l47x : ∀ (A B C : G), (A◇((A◇(A◇(A◇A)))◇B)) = ((A◇A)◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B)) := by
  intro A B C
  calc (A◇((A◇(A◇(A◇A)))◇B))
   _ = (A◇((A◇(A◇(A◇A)))◇((A◇A)◇((A◇A)◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B))))) := congrArg (A◇·) (congrArg ((A◇(A◇(A◇A)))◇·) ((l16 ((A◇A)) C B).symm))
   _ = ((A◇A)◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B)) := l42 A (((A◇A)◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B)))
 have l47 : ∀ (B C : G), ((B◇B)◇((B◇(B◇B))◇C)) = (B◇((B◇(B◇(B◇B)))◇C)) := by
  intro B C
  have strict_rw_6 := ((l47x B C B).symm)
  rw [l19, l12, l25] at strict_rw_6
  exact strict_rw_6
 have l48 : ∀ (B C D : G), (((B◇(C◇C))◇(C◇C))◇(C◇(C◇(C◇D)))) = (((B◇C)◇C)◇D) := by
  intro B C D
  calc (((B◇(C◇C))◇(C◇C))◇(C◇(C◇(C◇D))))
   _ = (((B◇(C◇C))◇(C◇C))◇((C◇C)◇(B◇(((B◇C)◇C)◇D)))) := congrArg (((B◇(C◇C))◇(C◇C))◇·) ((l43 C B D).symm)
   _ = (((B◇C)◇C)◇D) := l8 B ((C◇C)) ((((B◇C)◇C)◇D))
 have l49x : ∀ (A B C : G), ((((((A◇B)◇B)◇A)◇A)◇(A◇((A◇A)◇A)))◇C) = ((B◇A)◇C) := by
  intro A B C
  calc ((((((A◇B)◇B)◇A)◇A)◇(A◇((A◇A)◇A)))◇C)
   _ = ((((((A◇B)◇B)◇A)◇A)◇(A◇((A◇A)◇A)))◇(A◇((((A◇B)◇B)◇A)◇((B◇A)◇C)))) := congrArg ((((((A◇B)◇B)◇A)◇A)◇(A◇((A◇A)◇A)))◇·) ((l36 A B C).symm)
   _ = ((B◇A)◇C) := l44 ((((A◇B)◇B)◇A)) A (((B◇A)◇C))
 have l49 : ∀ (B C D : G), ((B◇(C◇((C◇C)◇C)))◇D) = ((B◇C)◇D) := by
  intro B C D
  have strict_rw_7 := (l49x C B D)
  rw [l4] at strict_rw_7
  exact strict_rw_7
 have l50x : ∀ (A B : G), (A◇((((A◇A)◇A)◇A)◇(A◇(A◇B)))) = (((A◇A)◇A)◇B) := by
  intro A B
  calc (A◇((((A◇A)◇A)◇A)◇(A◇(A◇B))))
   _ = (A◇((((A◇A)◇A)◇A)◇((A◇A)◇(((A◇A)◇A)◇B)))) := congrArg (A◇·) (congrArg ((((A◇A)◇A)◇A)◇·) ((l22 A B).symm))
   _ = (((A◇A)◇A)◇B) := l36 A A ((((A◇A)◇A)◇B))
 have l50 : ∀ (B C : G), (B◇(B◇(B◇((B◇(B◇(B◇B)))◇C)))) = (((B◇B)◇B)◇C) := by
  intro B C
  have strict_rw_8 := (l50x B C)
  rw [l37, l45, l46, l12, l47] at strict_rw_8
  exact strict_rw_8
 have l51 : ∀ (B C D : G), (((B◇(C◇C))◇(C◇C))◇(C◇D)) = (((B◇C)◇C)◇(((C◇C)◇C)◇D)) := by
  intro B C D
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46
  clear l47x l49x l50x
  grind
 have l52 : ∀ (B C D E : G), ((((((B◇C)◇C)◇D)◇D)◇D)◇E) = ((C◇(B◇((D◇D)◇D)))◇E) := by
  intro B C D E
  calc ((((((B◇C)◇C)◇D)◇D)◇D)◇E)
   _ = ((((((B◇C)◇C)◇D)◇D)◇(D◇((D◇D)◇D)))◇E) := (l49 (((((B◇C)◇C)◇D)◇D)) D E).symm
   _ = ((C◇(B◇((D◇D)◇D)))◇E) := congrArg (·◇E) (l6 B C D (((D◇D)◇D)))
 have l53 : ∀ (B C D E : G), (((B◇C)◇C)◇(C◇D)) = (((B◇E)◇E)◇(E◇D)) := by
  intro B C D E
  calc (((B◇C)◇C)◇(C◇D))
   _ = (((B◇C)◇C)◇(C◇(B◇(((B◇E)◇E)◇(E◇D))))) := congrArg (((B◇C)◇C)◇·) (congrArg (C◇·) ((l5 B E D).symm))
   _ = (((B◇E)◇E)◇(E◇D)) := l8 B C ((((B◇E)◇E)◇(E◇D)))
 have l54 : ∀ (B C D : G), ((((B◇(C◇C))◇(C◇C))◇C)◇D) = ((((B◇C)◇C)◇(C◇(C◇C)))◇D) := by
  intro B C D
  calc ((((B◇(C◇C))◇(C◇C))◇C)◇D)
   _ = ((((B◇(C◇C))◇(C◇C))◇(C◇((C◇C)◇C)))◇D) := (l49 (((B◇(C◇C))◇(C◇C))) C D).symm
   _ = ((((B◇C)◇C)◇(((C◇C)◇C)◇((C◇C)◇C)))◇D) := congrArg (·◇D) (l51 B C (((C◇C)◇C)))
   _ = ((((B◇C)◇C)◇(C◇(C◇C)))◇D) := congrArg (·◇D) (congrArg (((B◇C)◇C)◇·) (((l33 C C).symm).symm))
 have l55 : ∀ (B C D : G), ((B◇(C◇(C◇((C◇C)◇C))))◇D) = ((B◇(C◇C))◇D) := by
  intro B C D
  calc ((B◇(C◇(C◇((C◇C)◇C))))◇D)
   _ = ((B◇((C◇((C◇C)◇C))◇(C◇((C◇C)◇C))))◇D) := congrArg (·◇D) (congrArg (B◇·) ((l25 C ((C◇((C◇C)◇C)))).symm))
   _ = ((B◇(((C◇C)◇(C◇C))◇(C◇((C◇C)◇C))))◇D) := congrArg (·◇D) (congrArg (B◇·) (congrArg (·◇(C◇((C◇C)◇C))) ((l12 C C).symm)))
   _ = ((B◇(((C◇C)◇(C◇C))◇((C◇C)◇(C◇C))))◇D) := congrArg (·◇D) (congrArg (B◇·) (congrArg (((C◇C)◇(C◇C))◇·) ((l12 C C).symm)))
   _ = ((B◇((C◇C)◇(((C◇C)◇(C◇C))◇(C◇C))))◇D) := congrArg (·◇D) (congrArg (B◇·) (((l12 ((C◇C)) ((C◇C))).symm).symm))
   _ = ((B◇(C◇C))◇D) := ((l49 B ((C◇C)) D).symm).symm
 have l56 : ∀ (B C D : G), ((((B◇B)◇C)◇C)◇(C◇(B◇((B◇B)◇D)))) = (B◇D) := by
  intro B C D
  calc ((((B◇B)◇C)◇C)◇(C◇(B◇((B◇B)◇D))))
   _ = ((((B◇B)◇C)◇C)◇(C◇((B◇B)◇(B◇D)))) := congrArg ((((B◇B)◇C)◇C)◇·) (congrArg (C◇·) ((l12 B D).symm))
   _ = (B◇D) := l8 ((B◇B)) C ((B◇D))
 have l57 : ∀ (B C D : G), (((B◇B)◇B)◇C) = ((((B◇D)◇D)◇(D◇B))◇C) := by
  intro B C D
  calc (((B◇B)◇B)◇C)
   _ = (((B◇B)◇B)◇(B◇(B◇((((B◇D)◇D)◇(D◇B))◇C)))) := congrArg (((B◇B)◇B)◇·) ((l13 B D C).symm)
   _ = ((((B◇D)◇D)◇(D◇B))◇C) := l8 B B (((((B◇D)◇D)◇(D◇B))◇C))
 have l58 : ∀ (B C D : G), ((B◇(C◇((B◇B)◇B)))◇(B◇D)) = (B◇((C◇B)◇D)) := by
  intro B C D
  calc ((B◇(C◇((B◇B)◇B)))◇(B◇D))
   _ = ((((((C◇B)◇B)◇B)◇B)◇B)◇(B◇D)) := (l52 C B B ((B◇D))).symm
   _ = (B◇((C◇B)◇D)) := l6 ((C◇B)) B B D
 have l59 : ∀ (B C D : G), (((((B◇C)◇C)◇(C◇(C◇C)))◇C)◇(C◇D)) = ((C◇C)◇(B◇D)) := by
  intro B C D
  calc (((((B◇C)◇C)◇(C◇(C◇C)))◇C)◇(C◇D))
   _ = (((((B◇(C◇C))◇(C◇C))◇C)◇C)◇(C◇D)) := congrArg (·◇(C◇D)) ((l54 B C C).symm)
   _ = ((C◇C)◇(B◇D)) := l6 B ((C◇C)) C D
 have l60 : ∀ (B C : G), (((B◇B)◇B)◇(B◇((B◇(B◇B))◇C))) = (B◇(B◇((B◇B)◇C))) := by
  intro B C
  calc (((B◇B)◇B)◇(B◇((B◇(B◇B))◇C)))
   _ = (((B◇B)◇B)◇((B◇B)◇((B◇B)◇C))) := congrArg (((B◇B)◇B)◇·) ((l31 B C).symm)
   _ = (B◇(B◇((B◇B)◇C))) := l33 B (((B◇B)◇C))
 have l61 : ∀ (B C D E : G), ((B◇(C◇(D◇((D◇D)◇D))))◇E) = ((B◇(C◇D))◇E) := by
  intro B C D E
  calc ((B◇(C◇(D◇((D◇D)◇D))))◇E)
   _ = ((((((C◇B)◇B)◇D)◇D)◇(D◇(D◇((D◇D)◇D))))◇E) := congrArg (·◇E) ((l6 C B D ((D◇((D◇D)◇D)))).symm)
   _ = ((((((C◇B)◇B)◇D)◇D)◇(D◇D))◇E) := l55 (((((C◇B)◇B)◇D)◇D)) D E
   _ = ((B◇(C◇D))◇E) := congrArg (·◇E) (((l6 C B D D).symm).symm)
 have l62 : ∀ (B C : G), ((B◇(B◇(B◇B)))◇((B◇B)◇C)) = (B◇(((B◇B)◇B)◇C)) := by
  intro B C
  calc ((B◇(B◇(B◇B)))◇((B◇B)◇C))
   _ = ((((B◇B)◇B)◇B)◇((B◇B)◇C)) := (l37 B (((B◇B)◇C))).symm
   _ = ((((B◇B)◇B)◇B)◇(B◇(B◇((B◇B)◇(((B◇B)◇B)◇C))))) := congrArg ((((B◇B)◇B)◇B)◇·) ((l17 B C).symm)
   _ = (B◇(((B◇B)◇B)◇C)) := ((l56 B B ((((B◇B)◇B)◇C))).symm).symm
 have l63 : ∀ (B C D : G), ((((B◇B)◇B)◇(C◇B))◇((C◇B)◇D)) = (C◇(B◇D)) := by
  intro B C D
  calc ((((B◇B)◇B)◇(C◇B))◇((C◇B)◇D))
   _ = (((((B◇C)◇C)◇(C◇B))◇(C◇B))◇((C◇B)◇D)) := congrArg (·◇((C◇B)◇D)) (((l57 B ((C◇B)) C).symm).symm)
   _ = (C◇(B◇D)) := l6 B C ((C◇B)) D
 have l64 : ∀ (B C : G), (B◇((B◇(B◇B))◇((B◇(B◇B))◇C))) = C := by
  intro B C
  calc (B◇((B◇(B◇B))◇((B◇(B◇B))◇C)))
   _ = ((B◇B)◇((B◇B)◇((B◇(B◇B))◇C))) := (l31 B (((B◇(B◇B))◇C))).symm
   _ = C := l29 B C
 have l65 : ∀ (B C : G), ((B◇(B◇((B◇(B◇B))◇B)))◇C) = (((B◇B)◇B)◇C) := by
  intro B C
  calc ((B◇(B◇((B◇(B◇B))◇B)))◇C)
   _ = ((B◇((B◇B)◇((B◇B)◇B)))◇C) := congrArg (·◇C) (congrArg (B◇·) ((l31 B B).symm))
   _ = (((((B◇(B◇((B◇B)◇((B◇B)◇B))))◇(B◇((B◇B)◇((B◇B)◇B))))◇B)◇B)◇C) := (l4 B ((B◇((B◇B)◇((B◇B)◇B)))) C).symm
   _ = ((((B◇(B◇((B◇B)◇((B◇B)◇B))))◇B)◇B)◇C) := congrArg (·◇C) (congrArg (·◇B) (congrArg (·◇B) (((l28 B ((B◇((B◇B)◇((B◇B)◇B))))).symm).symm)))
   _ = (((B◇B)◇B)◇C) := congrArg (·◇C) (congrArg (·◇B) (((l28 B B).symm).symm))
 have l66x : ∀ (A B C : G), ((A◇(((A◇A)◇(A◇A))◇(B◇A)))◇(A◇C)) = (A◇((((((B◇(A◇A))◇(A◇A))◇((A◇A)◇((A◇A)◇(A◇A))))◇(A◇A))◇A)◇C)) := by
  intro A B C
  calc ((A◇(((A◇A)◇(A◇A))◇(B◇A)))◇(A◇C))
   _ = ((A◇(((((B◇(A◇A))◇(A◇A))◇((A◇A)◇((A◇A)◇(A◇A))))◇(A◇A))◇((A◇A)◇A)))◇(A◇C)) := congrArg (·◇(A◇C)) (congrArg (A◇·) ((l59 B ((A◇A)) A).symm))
   _ = (A◇((((((B◇(A◇A))◇(A◇A))◇((A◇A)◇((A◇A)◇(A◇A))))◇(A◇A))◇A)◇C)) := l58 A (((((B◇(A◇A))◇(A◇A))◇((A◇A)◇((A◇A)◇(A◇A))))◇(A◇A))) C
 have l66 : ∀ (B C D : G), ((B◇(B◇(C◇B)))◇(B◇D)) = (B◇((B◇(C◇(B◇B)))◇D)) := by
  intro B C D
  have strict_rw_9 := (l66x B C D)
  rw [l12, l25, l12, l31, l51, l60, l61, l54, l6] at strict_rw_9
  exact strict_rw_9
 have l67 : ∀ (B C D E : G), (B◇(((B◇((C◇D)◇D))◇((C◇D)◇D))◇E)) = (D◇(C◇E)) := by
  intro B C D E
  calc (B◇(((B◇((C◇D)◇D))◇((C◇D)◇D))◇E))
   _ = (D◇(C◇(((C◇D)◇D)◇(B◇(((B◇((C◇D)◇D))◇((C◇D)◇D))◇E))))) := ((l3 ((B◇(((B◇((C◇D)◇D))◇((C◇D)◇D))◇E))) D C).symm).symm
   _ = (D◇(C◇E)) := congrArg (D◇·) (congrArg (C◇·) ((l3 E (((C◇D)◇D)) B).symm))
 have l68 : ∀ (B C : G), ((B◇(B◇(B◇B)))◇(B◇C)) = (B◇((B◇(B◇(B◇B)))◇C)) := by
  intro B C
  calc ((B◇(B◇(B◇B)))◇(B◇C))
   _ = ((B◇B)◇((B◇(B◇B))◇C)) := ((l45 B C).symm).symm
   _ = (B◇((B◇(B◇(B◇B)))◇C)) := l47 B C
 have l69 : ∀ (B C : G), ((B◇(B◇(B◇B)))◇(((B◇B)◇B)◇C)) = (B◇((B◇(B◇B))◇C)) := by
  intro B C
  grind
 have l70x : ∀ (A B C D : G), ((A◇(B◇((((C◇C)◇C)◇((C◇C)◇C))◇(((C◇C)◇(C◇((C◇C)◇C)))◇(((C◇C)◇C)◇((C◇C)◇C))))))◇D) = ((A◇(B◇(((C◇C)◇C)◇((C◇C)◇C))))◇D) := by
  intro A B C D
  calc ((A◇(B◇((((C◇C)◇C)◇((C◇C)◇C))◇(((C◇C)◇(C◇((C◇C)◇C)))◇(((C◇C)◇C)◇((C◇C)◇C))))))◇D)
   _ = ((A◇(B◇((((C◇C)◇C)◇((C◇C)◇C))◇(((((C◇C)◇C)◇((C◇C)◇C))◇(((C◇C)◇C)◇((C◇C)◇C)))◇(((C◇C)◇C)◇((C◇C)◇C))))))◇D) := congrArg (·◇D) (congrArg (A◇·) (congrArg (B◇·) (congrArg ((((C◇C)◇C)◇((C◇C)◇C))◇·) (congrArg (·◇(((C◇C)◇C)◇((C◇C)◇C))) ((l63 C ((C◇C)) (((C◇C)◇C))).symm)))))
   _ = ((A◇(B◇(((C◇C)◇C)◇((C◇C)◇C))))◇D) := l61 A B ((((C◇C)◇C)◇((C◇C)◇C))) D
 have l70 : ∀ (B C D E : G), ((B◇(C◇((D◇(D◇D))◇D)))◇E) = ((B◇(C◇(D◇(D◇D))))◇E) := by
  intro B C D E
  have strict_rw_10 := (l70x B C D E)
  rw [l33, l12, l31, l65, l8] at strict_rw_10
  exact strict_rw_10
 have l71 : ∀ (B C D E : G), ((B◇(C◇(D◇B)))◇(B◇E)) = (B◇((C◇(D◇(B◇B)))◇E)) := by
  intro B C D E
  calc ((B◇(C◇(D◇B)))◇(B◇E))
   _ = ((B◇(B◇(((B◇((D◇C)◇C))◇((D◇C)◇C))◇B)))◇(B◇E)) := congrArg (·◇(B◇E)) (congrArg (B◇·) ((l67 B D C B).symm))
   _ = (B◇((B◇(((B◇((D◇C)◇C))◇((D◇C)◇C))◇(B◇B)))◇E)) := l66 B (((B◇((D◇C)◇C))◇((D◇C)◇C))) E
   _ = (B◇((C◇(D◇(B◇B)))◇E)) := congrArg (B◇·) (congrArg (·◇E) (((l67 B D C ((B◇B))).symm).symm))
 have l72 : ∀ (B C D : G), ((B◇(C◇((C◇(C◇C))◇C)))◇D) = ((B◇(C◇(C◇(C◇C))))◇D) := by
  intro B C D
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45
  clear l46 l47x l47 l48 l49x l50x l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67
  clear l70x l70 l71
  grind
 have l73 : ∀ (B C D : G), ((B◇(C◇(B◇(B◇B))))◇(B◇D)) = (B◇((C◇(B◇(B◇(B◇B))))◇D)) := by
  intro B C D
  calc ((B◇(C◇(B◇(B◇B))))◇(B◇D))
   _ = ((B◇(C◇((B◇(B◇B))◇B)))◇(B◇D)) := (l70 B C B ((B◇D))).symm
   _ = (B◇((C◇((B◇(B◇B))◇(B◇B)))◇D)) := l71 B C ((B◇(B◇B))) D
   _ = (B◇((C◇(B◇((B◇(B◇B))◇B)))◇D)) := congrArg (B◇·) (congrArg (·◇D) (congrArg (C◇·) (((l46 B B).symm).symm)))
   _ = (B◇((C◇(B◇(B◇(B◇B))))◇D)) := congrArg (B◇·) (((l70 C B B D).symm).symm)
 have l74x : ∀ (A B C : G), (A◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇C)))) = (((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇(((((A◇B)◇B)◇(B◇A))◇A)◇A))◇C) := by
  intro A B C
  calc (A◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇C))))
   _ = ((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇C)))) := (l11 A B (((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇C))))).symm
   _ = (((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇(((((A◇B)◇B)◇(B◇A))◇A)◇A))◇C) := l23 ((((((A◇B)◇B)◇(B◇A))◇A)◇A)) C
 have l74 : ∀ (B C D : G), ((B◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇D) = ((B◇B)◇D) := by
  intro B C D
  have strict_rw_11 := ((l74x B C D).symm)
  rw [l11, l11, l11, l11, l23] at strict_rw_11
  exact strict_rw_11
 have l75x : ∀ (A B C : G), ((A◇A)◇(A◇(((((A◇B)◇B)◇(B◇A))◇A)◇C))) = C := by
  intro A B C
  calc ((A◇A)◇(A◇(((((A◇B)◇B)◇(B◇A))◇A)◇C)))
   _ = (((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇A)◇(A◇(((((A◇B)◇B)◇(B◇A))◇A)◇C))) := congrArg (·◇(A◇(((((A◇B)◇B)◇(B◇A))◇A)◇C))) ((l11 A B A).symm)
   _ = C := l8 (((((A◇B)◇B)◇(B◇A))◇A)) A C
 have l75 : ∀ (B C D : G), (B◇((B◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇D))) = D := by
  intro B C D
  have strict_rw_12 := (l75x B C D)
  rw [l12] at strict_rw_12
  exact strict_rw_12
 have l76x : ∀ (A B C : G), ((((((A◇B)◇B)◇A)◇A)◇(A◇((A◇(B◇A))◇(B◇A))))◇C) = (A◇C) := by
  intro A B C
  calc ((((((A◇B)◇B)◇A)◇A)◇(A◇((A◇(B◇A))◇(B◇A))))◇C)
   _ = (((((A◇(B◇A))◇(B◇A))◇A)◇(A◇((A◇(B◇A))◇(B◇A))))◇C) := congrArg (·◇C) (congrArg (·◇(A◇((A◇(B◇A))◇(B◇A)))) ((l40 A B A).symm))
   _ = (A◇C) := l9 ((A◇(B◇A))) B A C
 have l76 : ∀ (B C D : G), ((B◇(C◇((C◇(B◇C))◇(B◇C))))◇D) = (C◇D) := by
  intro B C D
  have strict_rw_13 := (l76x C B D)
  rw [l4] at strict_rw_13
  exact strict_rw_13
 have l77 : ∀ (B C D : G), (((((B◇B)◇C)◇C)◇(C◇B))◇(B◇D)) = (B◇((B◇B)◇D)) := by
  intro B C D
  calc (((((B◇B)◇C)◇C)◇(C◇B))◇(B◇D))
   _ = (((((B◇B)◇B)◇B)◇(B◇B))◇(B◇D)) := congrArg (·◇(B◇D)) ((l53 ((B◇B)) B B C).symm)
   _ = (B◇((B◇B)◇D)) := l35 B B D
 have l78x : ∀ (A B C : G), (((A◇(A◇A))◇(A◇A))◇B) = (A◇(A◇(A◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B)))) := by
  intro A B C
  calc (((A◇(A◇A))◇(A◇A))◇B)
   _ = (((A◇(A◇A))◇(A◇A))◇((A◇A)◇((A◇A)◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B)))) := congrArg (((A◇(A◇A))◇(A◇A))◇·) ((l16 ((A◇A)) C B).symm)
   _ = (A◇(A◇(A◇((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B)))) := l27 A ((A◇A)) (((C◇(((C◇(A◇A))◇(A◇A))◇(A◇A)))◇B))
 have l78 : ∀ (B C : G), (B◇(B◇(B◇((B◇(B◇B))◇C)))) = ((B◇(B◇(B◇B)))◇C) := by
  intro B C
  have hx := ((l78x B C B).symm)
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l20 l21 l22 l23 l24x l24
  clear l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l38 l39 l41x l41 l42 l43 l44x l44 l45 l46 l47x l47 l48
  clear l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67 l68 l69
  clear l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x
  grind
 have l79 : ∀ (B C D E : G), ((B◇(C◇(D◇(B◇B))))◇(B◇E)) = (B◇((C◇(D◇(B◇(B◇B))))◇E)) := by
  intro B C D E
  calc ((B◇(C◇(D◇(B◇B))))◇(B◇E))
   _ = ((B◇(((((D◇C)◇C)◇B)◇B)◇(B◇(B◇B))))◇(B◇E)) := congrArg (·◇(B◇E)) (congrArg (B◇·) ((l6 D C B ((B◇B))).symm))
   _ = (B◇((((((D◇C)◇C)◇B)◇B)◇(B◇(B◇(B◇B))))◇E)) := l73 B (((((D◇C)◇C)◇B)◇B)) E
   _ = (B◇((C◇(D◇(B◇(B◇B))))◇E)) := congrArg (B◇·) (congrArg (·◇E) (((l6 D C B ((B◇(B◇B)))).symm).symm))
 have l80 : ∀ (B C D : G), ((B◇(C◇B))◇(((C◇B)◇((C◇B)◇B))◇D)) = (B◇(C◇D)) := by
  intro B C D
  calc ((B◇(C◇B))◇(((C◇B)◇((C◇B)◇B))◇D))
   _ = ((B◇(C◇B))◇((((B◇(C◇B))◇((C◇B)◇B))◇((C◇B)◇B))◇D)) := congrArg ((B◇(C◇B))◇·) (congrArg (·◇D) ((l7 B C (((C◇B)◇B))).symm))
   _ = (((((C◇B)◇B)◇B)◇B)◇(B◇D)) := l38 ((B◇(C◇B))) (((C◇B)◇B)) D B
   _ = (B◇(C◇D)) := ((l6 C B B D).symm).symm
 have l81x : ∀ (A B C D : G), ((A◇(B◇(((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))))◇D) = ((A◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇D) := by
  intro A B C D
  calc ((A◇(B◇(((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))))◇D)
   _ = ((A◇((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇(((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))))◇D) := congrArg (·◇D) (congrArg (A◇·) ((l11 B C ((((((((B◇C)◇C)◇(C◇B))◇B)◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇(((((B◇C)◇C)◇(C◇B))◇B)◇B)))).symm))
   _ = ((A◇(((((B◇C)◇C)◇(C◇B))◇B)◇B))◇D) := l49 A ((((((B◇C)◇C)◇(C◇B))◇B)◇B)) D
 have l81 : ∀ (B C D E : G), ((B◇(((((C◇D)◇D)◇(D◇C))◇C)◇C))◇E) = ((B◇C)◇E) := by
  intro B C D E
  have strict_rw_14 := ((l81x B C D E).symm)
  rw [l11, l74, l75] at strict_rw_14
  exact strict_rw_14
 have l82 : ∀ (B C D : G), (B◇((((B◇C)◇C)◇(C◇B))◇D)) = (((B◇C)◇C)◇(C◇D)) := by
  intro B C D
  calc (B◇((((B◇C)◇C)◇(C◇B))◇D))
   _ = ((B◇(((B◇C)◇C)◇(C◇B)))◇((((B◇C)◇C)◇(C◇B))◇D)) := congrArg (·◇((((B◇C)◇C)◇(C◇B))◇D)) ((l5 B C B).symm)
   _ = (((B◇C)◇C)◇(C◇D)) := l14 B (((B◇C)◇C)) C D
 have l83 : ∀ (B C D : G), (((((B◇B)◇C)◇C)◇(C◇B))◇D) = ((B◇B)◇D) := by
  intro B C D
  grind
 have l84 : ∀ (B C D : G), ((B◇((C◇(C◇(C◇C)))◇C))◇D) = ((B◇C)◇D) := by
  intro B C D
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l26 l27 l28 l29 l30 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46 l47x
  clear l47 l48 l49x l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67 l68
  clear l69 l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l79 l80 l81x l81 l82 l83
  grind
 have l85 : ∀ (B C D E F : G), ((B◇(C◇(D◇(E◇B))))◇(B◇F)) = (B◇((C◇(D◇(E◇(B◇B))))◇F)) := by
  intro B C D E F
  calc ((B◇(C◇(D◇(E◇B))))◇(B◇F))
   _ = ((B◇(C◇(((((E◇D)◇D)◇B)◇B)◇(B◇B))))◇(B◇F)) := congrArg (·◇(B◇F)) (congrArg (B◇·) (congrArg (C◇·) ((l6 E D B B).symm)))
   _ = (B◇((C◇(((((E◇D)◇D)◇B)◇B)◇(B◇(B◇B))))◇F)) := l79 B C (((((E◇D)◇D)◇B)◇B)) F
   _ = (B◇((C◇(D◇(E◇(B◇B))))◇F)) := congrArg (B◇·) (congrArg (·◇F) (congrArg (C◇·) (((l6 E D B ((B◇B))).symm).symm)))
 have l86x : ∀ (A B C D : G), ((((A◇((((B◇C)◇C)◇A)◇A))◇((((B◇C)◇C)◇A)◇A))◇A)◇((C◇(B◇((A◇A)◇A)))◇(A◇D))) = D := by
  intro A B C D
  calc ((((A◇((((B◇C)◇C)◇A)◇A))◇((((B◇C)◇C)◇A)◇A))◇A)◇((C◇(B◇((A◇A)◇A)))◇(A◇D)))
   _ = ((((A◇((((B◇C)◇C)◇A)◇A))◇((((B◇C)◇C)◇A)◇A))◇A)◇((((((B◇C)◇C)◇A)◇A)◇A)◇(A◇D))) := congrArg ((((A◇((((B◇C)◇C)◇A)◇A))◇((((B◇C)◇C)◇A)◇A))◇A)◇·) ((l52 B C A ((A◇D))).symm)
   _ = D := l10 A (((((B◇C)◇C)◇A)◇A)) D
 have l86 : ∀ (B C D E : G), ((((B◇C)◇C)◇D)◇((C◇(B◇((D◇D)◇D)))◇(D◇E))) = E := by
  intro B C D E
  have strict_rw_15 := (l86x D B C E)
  rw [l40, l4] at strict_rw_15
  exact strict_rw_15
 have l87x : ∀ (A B C : G), ((A◇((((A◇B)◇B)◇(B◇A))◇A))◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇C)) = (A◇((((A◇B)◇B)◇(B◇A))◇C)) := by
  intro A B C
  calc ((A◇((((A◇B)◇B)◇(B◇A))◇A))◇((((((A◇B)◇B)◇(B◇A))◇A)◇A)◇C))
   _ = ((A◇((((A◇B)◇B)◇(B◇A))◇A))◇((((((A◇B)◇B)◇(B◇A))◇A)◇(((((A◇B)◇B)◇(B◇A))◇A)◇A))◇C)) := congrArg ((A◇((((A◇B)◇B)◇(B◇A))◇A))◇·) ((l81 (((((A◇B)◇B)◇(B◇A))◇A)) A B C).symm)
   _ = (A◇((((A◇B)◇B)◇(B◇A))◇C)) := l80 A ((((A◇B)◇B)◇(B◇A))) C
 have l87 : ∀ (B C D : G), ((((B◇C)◇C)◇(C◇B))◇(B◇D)) = (((B◇C)◇C)◇(C◇D)) := by
  intro B C D
  have strict_rw_16 := (l87x B C D)
  rw [l82, l11, l82] at strict_rw_16
  exact strict_rw_16
 have l88 : ∀ (B C D : G), (((((B◇B)◇C)◇C)◇(C◇(B◇B)))◇D) = ((B◇(B◇B))◇D) := by
  intro B C D
  calc (((((B◇B)◇C)◇C)◇(C◇(B◇B)))◇D)
   _ = ((((B◇B)◇(B◇B))◇(B◇B))◇D) := (l57 ((B◇B)) D C).symm
   _ = (((B◇((B◇B)◇B))◇(B◇B))◇D) := congrArg (·◇D) (congrArg (·◇(B◇B)) (l12 B B))
   _ = ((B◇(B◇B))◇D) := congrArg (·◇D) (((l25 B ((B◇B))).symm).symm)
 have l89x : ∀ (A B C D : G), ((A◇((B◇B)◇((((((B◇B)◇C)◇C)◇(C◇B))◇((((B◇B)◇C)◇C)◇(C◇B)))◇((((B◇B)◇C)◇C)◇(C◇B)))))◇D) = ((A◇((((B◇B)◇C)◇C)◇(C◇B)))◇D) := by
  intro A B C D
  calc ((A◇((B◇B)◇((((((B◇B)◇C)◇C)◇(C◇B))◇((((B◇B)◇C)◇C)◇(C◇B)))◇((((B◇B)◇C)◇C)◇(C◇B)))))◇D)
   _ = ((A◇(((((B◇B)◇C)◇C)◇(C◇B))◇((((((B◇B)◇C)◇C)◇(C◇B))◇((((B◇B)◇C)◇C)◇(C◇B)))◇((((B◇B)◇C)◇C)◇(C◇B)))))◇D) := congrArg (·◇D) (congrArg (A◇·) ((l83 B C (((((((B◇B)◇C)◇C)◇(C◇B))◇((((B◇B)◇C)◇C)◇(C◇B)))◇((((B◇B)◇C)◇C)◇(C◇B))))).symm))
   _ = ((A◇((((B◇B)◇C)◇C)◇(C◇B)))◇D) := l49 A (((((B◇B)◇C)◇C)◇(C◇B))) D
 have l89 : ∀ (B C D E : G), ((B◇((((C◇C)◇D)◇D)◇(D◇C)))◇E) = ((B◇(C◇C))◇E) := by
  intro B C D E
  have strict_rw_17 := ((l89x B C D E).symm)
  rw [l83, l5, l12, l5] at strict_rw_17
  exact strict_rw_17
 have l90 : ∀ (B C D E : G), ((B◇(C◇(D◇(D◇((D◇D)◇D)))))◇E) = ((B◇(C◇(D◇D)))◇E) := by
  intro B C D E
  calc ((B◇(C◇(D◇(D◇((D◇D)◇D)))))◇E)
   _ = ((B◇(C◇((D◇((D◇D)◇D))◇(D◇((D◇D)◇D)))))◇E) := congrArg (·◇E) (congrArg (B◇·) (congrArg (C◇·) ((l25 D ((D◇((D◇D)◇D)))).symm)))
   _ = ((B◇(C◇(((D◇D)◇(D◇D))◇(D◇((D◇D)◇D)))))◇E) := congrArg (·◇E) (congrArg (B◇·) (congrArg (C◇·) (congrArg (·◇(D◇((D◇D)◇D))) ((l12 D D).symm))))
   _ = ((B◇(C◇(((D◇D)◇(D◇D))◇((D◇D)◇(D◇D)))))◇E) := congrArg (·◇E) (congrArg (B◇·) (congrArg (C◇·) (congrArg (((D◇D)◇(D◇D))◇·) ((l12 D D).symm))))
   _ = ((B◇(C◇((D◇D)◇(((D◇D)◇(D◇D))◇(D◇D)))))◇E) := congrArg (·◇E) (congrArg (B◇·) (congrArg (C◇·) (((l12 ((D◇D)) ((D◇D))).symm).symm)))
   _ = ((B◇(C◇(D◇D)))◇E) := ((l61 B C ((D◇D)) E).symm).symm
 have l91 : ∀ (B C D E : G), ((((((B◇C)◇C)◇B)◇D)◇D)◇(D◇E)) = ((C◇B)◇(B◇E)) := by
  intro B C D E
  calc ((((((B◇C)◇C)◇B)◇D)◇D)◇(D◇E))
   _ = ((((((B◇C)◇C)◇B)◇D)◇D)◇(D◇((((B◇C)◇C)◇B)◇((C◇B)◇(B◇E))))) := congrArg ((((((B◇C)◇C)◇B)◇D)◇D)◇·) (congrArg (D◇·) ((l10 B C E).symm))
   _ = ((C◇B)◇(B◇E)) := l8 ((((B◇C)◇C)◇B)) D (((C◇B)◇(B◇E)))
 have l92x : ∀ (A B C : G), ((A◇((((B◇B)◇B)◇(((B◇B)◇B)◇(B◇(B◇B))))◇((B◇B)◇B)))◇C) = ((A◇((B◇B)◇B))◇C) := by
  intro A B C
  calc ((A◇((((B◇B)◇B)◇(((B◇B)◇B)◇(B◇(B◇B))))◇((B◇B)◇B)))◇C)
   _ = ((A◇((((B◇B)◇B)◇(((B◇B)◇B)◇(((B◇B)◇B)◇((B◇B)◇B))))◇((B◇B)◇B)))◇C) := congrArg (·◇C) (congrArg (A◇·) (congrArg (·◇((B◇B)◇B)) (congrArg (((B◇B)◇B)◇·) (congrArg (((B◇B)◇B)◇·) ((l33 B B).symm)))))
   _ = ((A◇((B◇B)◇B))◇C) := l84 A (((B◇B)◇B)) C
 have l92 : ∀ (B C D : G), ((B◇(C◇(((C◇C)◇C)◇C)))◇D) = ((B◇((C◇C)◇C))◇D) := by
  intro B C D
  have strict_rw_18 := (l92x B C D)
  rw [l8, l37, l62] at strict_rw_18
  exact strict_rw_18
 have l93 : ∀ (B C D E : G), (B◇(((B◇C)◇C)◇D)) = (E◇(((E◇C)◇C)◇D)) := by
  intro B C D E
  calc (B◇(((B◇C)◇C)◇D))
   _ = (B◇(((B◇C)◇C)◇(C◇(E◇(((E◇C)◇C)◇D))))) := congrArg (B◇·) (congrArg (((B◇C)◇C)◇·) (((l3 D C E).symm).symm))
   _ = (E◇(((E◇C)◇C)◇D)) := l5 B C ((E◇(((E◇C)◇C)◇D)))
 have l94 : ∀ (B C D E : G), (B◇((((B◇C)◇C)◇(C◇(D◇(B◇B))))◇E)) = ((D◇B)◇(B◇E)) := by
  intro B C D E
  calc (B◇((((B◇C)◇C)◇(C◇(D◇(B◇B))))◇E))
   _ = ((B◇(((B◇C)◇C)◇(C◇(D◇B))))◇(B◇E)) := (l85 B (((B◇C)◇C)) C D E).symm
   _ = ((D◇B)◇(B◇E)) := congrArg (·◇(B◇E)) (l5 B C ((D◇B)))
 have l95 : ∀ (B C D : G), (((((B◇(B◇B))◇C)◇C)◇B)◇((C◇(B◇B))◇(B◇D))) = D := by
  intro B C D
  calc (((((B◇(B◇B))◇C)◇C)◇B)◇((C◇(B◇B))◇(B◇D)))
   _ = ((((((((B◇B)◇B)◇B)◇(B◇(B◇B)))◇C)◇C)◇B)◇((C◇(B◇B))◇(B◇D))) := congrArg (·◇((C◇(B◇B))◇(B◇D))) (congrArg (·◇B) (congrArg (·◇C) ((l88 B B C).symm)))
   _ = ((((((((B◇B)◇B)◇B)◇(B◇(B◇B)))◇C)◇C)◇B)◇((C◇((((B◇B)◇B)◇B)◇(B◇B)))◇(B◇D))) := congrArg ((((((((B◇B)◇B)◇B)◇(B◇(B◇B)))◇C)◇C)◇B)◇·) ((l89 C B B ((B◇D))).symm)
   _ = ((((((((B◇B)◇B)◇B)◇(B◇(B◇B)))◇C)◇C)◇B)◇((C◇(((((B◇B)◇B)◇B)◇(B◇(B◇B)))◇((B◇B)◇B)))◇(B◇D))) := congrArg ((((((((B◇B)◇B)◇B)◇(B◇(B◇B)))◇C)◇C)◇B)◇·) (congrArg (·◇(B◇D)) (congrArg (C◇·) ((l87 ((B◇B)) B B).symm)))
   _ = D := l86 (((((B◇B)◇B)◇B)◇(B◇(B◇B)))) C B D
 have l96 : ∀ (B C : G), (B◇(B◇(B◇((B◇B)◇C)))) = ((B◇(B◇B))◇C) := by
  intro B C
  calc (B◇(B◇(B◇((B◇B)◇C))))
   _ = (((B◇B)◇B)◇(B◇((B◇B)◇((B◇B)◇C)))) := (l27 B B (((B◇B)◇C))).symm
   _ = (((B◇B)◇B)◇(B◇(B◇((B◇(B◇B))◇C)))) := congrArg (((B◇B)◇B)◇·) (congrArg (B◇·) (l31 B C))
   _ = ((B◇(B◇B))◇C) := ((l8 B B (((B◇(B◇B))◇C))).symm).symm
 have l97 : ∀ (B C D E F : G), ((B◇(C◇(D◇(E◇((E◇E)◇E)))))◇F) = ((B◇(C◇(D◇E)))◇F) := by
  intro B C D E F
  calc ((B◇(C◇(D◇(E◇((E◇E)◇E)))))◇F)
   _ = ((B◇(((((D◇C)◇C)◇E)◇E)◇(E◇(E◇((E◇E)◇E)))))◇F) := congrArg (·◇F) (congrArg (B◇·) ((l6 D C E ((E◇((E◇E)◇E)))).symm))
   _ = ((B◇(((((D◇C)◇C)◇E)◇E)◇(E◇E)))◇F) := l90 B (((((D◇C)◇C)◇E)◇E)) E F
   _ = ((B◇(C◇(D◇E)))◇F) := congrArg (·◇F) (congrArg (B◇·) (((l6 D C E E).symm).symm))
 have l98x : ∀ (A B C D : G), (((((((A◇B)◇B)◇B)◇(A◇B))◇C)◇C)◇(C◇(B◇((B◇B)◇D)))) = (A◇D) := by
  intro A B C D
  calc (((((((A◇B)◇B)◇B)◇(A◇B))◇C)◇C)◇(C◇(B◇((B◇B)◇D))))
   _ = (((((((A◇B)◇B)◇B)◇(A◇B))◇C)◇C)◇(C◇(((((A◇B)◇B)◇B)◇(A◇B))◇(A◇D)))) := congrArg (((((((A◇B)◇B)◇B)◇(A◇B))◇C)◇C)◇·) (congrArg (C◇·) ((l35 A B D).symm))
   _ = (A◇D) := l8 (((((A◇B)◇B)◇B)◇(A◇B))) C ((A◇D))
 have l98 : ∀ (B C D : G), ((B◇(C◇B))◇((C◇B)◇(B◇((B◇B)◇D)))) = (C◇D) := by
  intro B C D
  have strict_rw_19 := (l98x C B B D)
  rw [l91] at strict_rw_19
  exact strict_rw_19
 have l99 : ∀ (B C D E : G), (((B◇(((B◇(C◇D))◇(C◇D))◇D))◇(C◇D))◇E) = (C◇E) := by
  intro B C D E
  calc (((B◇(((B◇(C◇D))◇(C◇D))◇D))◇(C◇D))◇E)
   _ = ((((((C◇D)◇C)◇C)◇(C◇D))◇(C◇D))◇E) := congrArg (·◇E) (congrArg (·◇(C◇D)) (((l38 B ((C◇D)) D C).symm).symm))
   _ = (C◇E) := l4 ((C◇D)) C E
 have l100 : ∀ (B C D E : G), ((B◇(C◇(((C◇D)◇D)◇D)))◇E) = ((B◇((D◇D)◇D))◇E) := by
  intro B C D E
  calc ((B◇(C◇(((C◇D)◇D)◇D)))◇E)
   _ = ((B◇(D◇(((D◇D)◇D)◇D)))◇E) := congrArg (·◇E) (congrArg (B◇·) ((l93 D D D C).symm))
   _ = ((B◇((D◇D)◇D))◇E) := l92 B D E
 have l101 : ∀ (B C D : G), (B◇(B◇(B◇((((B◇B)◇C)◇C)◇D)))) = (((B◇C)◇C)◇D) := by
  intro B C D
  calc (B◇(B◇(B◇((((B◇B)◇C)◇C)◇D))))
   _ = (((B◇C)◇C)◇(C◇((B◇B)◇((((B◇B)◇C)◇C)◇D)))) := (l27 B C (((((B◇B)◇C)◇C)◇D))).symm
   _ = (((B◇C)◇C)◇D) := congrArg (((B◇C)◇C)◇·) ((l3 D C ((B◇B))).symm)
 have l102 : ∀ (B C D : G), (((B◇B)◇(C◇B))◇((C◇B)◇D)) = (C◇((B◇B)◇D)) := by
  intro B C D
  calc (((B◇B)◇(C◇B))◇((C◇B)◇D))
   _ = ((((((B◇B)◇C)◇C)◇(C◇B))◇(C◇B))◇((C◇B)◇D)) := congrArg (·◇((C◇B)◇D)) ((l83 B C ((C◇B))).symm)
   _ = (C◇((B◇B)◇D)) := l6 ((B◇B)) C ((C◇B)) D
 have l103x : ∀ (A B C D : G), ((((((A◇B)◇B)◇C)◇C)◇(C◇((A◇B)◇B)))◇D) = (B◇(A◇(((((A◇B)◇B)◇C)◇C)◇(C◇D)))) := by
  intro A B C D
  calc ((((((A◇B)◇B)◇C)◇C)◇(C◇((A◇B)◇B)))◇D)
   _ = (B◇(A◇(((A◇B)◇B)◇((((((A◇B)◇B)◇C)◇C)◇(C◇((A◇B)◇B)))◇D)))) := l3 (((((((A◇B)◇B)◇C)◇C)◇(C◇((A◇B)◇B)))◇D)) B A
   _ = (B◇(A◇(((((A◇B)◇B)◇C)◇C)◇(C◇D)))) := congrArg (B◇·) (congrArg (A◇·) (l82 (((A◇B)◇B)) C D))
 have l103 : ∀ (B C D : G), ((B◇(C◇((C◇B)◇B)))◇D) = (B◇(C◇(B◇(C◇D)))) := by
  intro B C D
  have strict_rw_20 := (l103x C B B D)
  rw [l6, l6] at strict_rw_20
  exact strict_rw_20
 have l104x : ∀ (A B C : G), (A◇((((A◇((((A◇(A◇A))◇B)◇B)◇A))◇((((A◇(A◇A))◇B)◇B)◇A))◇A)◇C)) = (((B◇(A◇A))◇A)◇(A◇C)) := by
  intro A B C
  calc (A◇((((A◇((((A◇(A◇A))◇B)◇B)◇A))◇((((A◇(A◇A))◇B)◇B)◇A))◇A)◇C))
   _ = (A◇((((A◇((((A◇(A◇A))◇B)◇B)◇A))◇((((A◇(A◇A))◇B)◇B)◇A))◇(((((A◇(A◇A))◇B)◇B)◇A)◇((B◇(A◇A))◇(A◇A))))◇C)) := congrArg (A◇·) (congrArg (·◇C) (congrArg (((A◇((((A◇(A◇A))◇B)◇B)◇A))◇((((A◇(A◇A))◇B)◇B)◇A))◇·) ((l95 A B A).symm)))
   _ = (((B◇(A◇A))◇A)◇(A◇C)) := l94 A (((((A◇(A◇A))◇B)◇B)◇A)) ((B◇(A◇A))) C
 have l104 : ∀ (B C D : G), (B◇((((B◇(B◇B))◇C)◇C)◇D)) = (((C◇(B◇B))◇B)◇(B◇D)) := by
  intro B C D
  have strict_rw_21 := (l104x B C D)
  rw [l40, l4] at strict_rw_21
  exact strict_rw_21
 have l105 : ∀ (B C D : G), (((B◇C)◇C)◇(C◇((B◇(B◇B))◇D))) = (B◇(B◇((B◇B)◇D))) := by
  intro B C D
  calc (((B◇C)◇C)◇(C◇((B◇(B◇B))◇D)))
   _ = (((B◇C)◇C)◇(C◇(B◇(B◇(B◇((B◇B)◇D)))))) := congrArg (((B◇C)◇C)◇·) (congrArg (C◇·) ((l96 B D).symm))
   _ = (B◇(B◇((B◇B)◇D))) := l8 B C ((B◇(B◇((B◇B)◇D))))
 have l106 : ∀ (B C : G), ((B◇(B◇B))◇(((B◇B)◇B)◇C)) = (B◇((B◇B)◇C)) := by
  intro B C
  calc ((B◇(B◇B))◇(((B◇B)◇B)◇C))
   _ = (B◇(B◇(B◇((B◇B)◇(((B◇B)◇B)◇C))))) := (l96 B ((((B◇B)◇B)◇C))).symm
   _ = (B◇(B◇(B◇(B◇(B◇C))))) := congrArg (B◇·) (congrArg (B◇·) (congrArg (B◇·) (l22 B C)))
   _ = (B◇((B◇B)◇C)) := congrArg (B◇·) (((l23 B C).symm).symm)
 have l107 : ∀ (B C : G), ((B◇(B◇B))◇((B◇B)◇C)) = ((B◇B)◇((B◇(B◇B))◇C)) := by
  intro B C
  clear h l4 l5 l6 l8 l9 l10 l11 l12 l13 l14x l14 l15 l16x l16 l18 l19 l21 l23 l24x l24 l25 l26 l27
  clear l28 l29 l30 l31 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46 l47x l47 l48
  clear l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67 l68 l69
  clear l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l78 l79 l80 l81x l81 l82 l83 l84 l85 l86x l86
  clear l87x l87 l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l96 l97 l98x l98 l99 l100 l101 l102 l103x l103 l104x l104
  clear l105 l106
  grind
 have l108 : ∀ (B C D E : G), ((B◇((C◇(D◇C))◇((D◇C)◇C)))◇E) = ((B◇(D◇C))◇E) := by
  intro B C D E
  calc ((B◇((C◇(D◇C))◇((D◇C)◇C)))◇E)
   _ = ((B◇((C◇(D◇C))◇((D◇C)◇(C◇((C◇C)◇C)))))◇E) := (l97 B ((C◇(D◇C))) ((D◇C)) C E).symm
   _ = ((B◇(D◇C))◇E) := congrArg (·◇E) (congrArg (B◇·) (l98 C D C))
 have l109x : ∀ (A B C D E : G), A = ((B◇(C◇((D◇D)◇D)))◇(E◇(((E◇(((((C◇B)◇B)◇D)◇D)◇D))◇(((((C◇B)◇B)◇D)◇D)◇D))◇A))) := by
  intro A B C D E
  calc A
   _ = ((((((C◇B)◇B)◇D)◇D)◇D)◇(E◇(((E◇(((((C◇B)◇B)◇D)◇D)◇D))◇(((((C◇B)◇B)◇D)◇D)◇D))◇A))) := ((l3 A ((((((C◇B)◇B)◇D)◇D)◇D)) E).symm).symm
   _ = ((B◇(C◇((D◇D)◇D)))◇(E◇(((E◇(((((C◇B)◇B)◇D)◇D)◇D))◇(((((C◇B)◇B)◇D)◇D)◇D))◇A))) := l52 C B D ((E◇(((E◇(((((C◇B)◇B)◇D)◇D)◇D))◇(((((C◇B)◇B)◇D)◇D)◇D))◇A)))
 have l109 : ∀ (B C D E : G), ((B◇(C◇((D◇D)◇D)))◇(D◇((((C◇B)◇B)◇D)◇E))) = E := by
  intro B C D E
  have strict_rw_22 := ((l109x E B C D B).symm)
  rw [l67] at strict_rw_22
  exact strict_rw_22
 have l110x : ∀ (A B C D : G), (A◇B) = (((C◇(((C◇(A◇(((A◇D)◇D)◇D)))◇(A◇(((A◇D)◇D)◇D)))◇(((A◇D)◇D)◇D)))◇((D◇D)◇D))◇B) := by
  intro A B C D
  calc (A◇B)
   _ = (((C◇(((C◇(A◇(((A◇D)◇D)◇D)))◇(A◇(((A◇D)◇D)◇D)))◇(((A◇D)◇D)◇D)))◇(A◇(((A◇D)◇D)◇D)))◇B) := (l99 C A ((((A◇D)◇D)◇D)) B).symm
   _ = (((C◇(((C◇(A◇(((A◇D)◇D)◇D)))◇(A◇(((A◇D)◇D)◇D)))◇(((A◇D)◇D)◇D)))◇((D◇D)◇D))◇B) := l100 ((C◇(((C◇(A◇(((A◇D)◇D)◇D)))◇(A◇(((A◇D)◇D)◇D)))◇(((A◇D)◇D)◇D)))) A D B
 have l110 : ∀ (B C D : G), (((B◇(B◇(((C◇B)◇B)◇B)))◇((B◇B)◇B))◇D) = (C◇D) := by
  intro B C D
  have strict_rw_23 := ((l110x C D B B).symm)
  rw [l100, l100, l67] at strict_rw_23
  exact strict_rw_23
 have l111 : ∀ (B C D : G), (((B◇B)◇B)◇(((B◇C)◇C)◇D)) = (B◇((((B◇B)◇C)◇C)◇D)) := by
  intro B C D
  calc (((B◇B)◇B)◇(((B◇C)◇C)◇D))
   _ = (((B◇B)◇B)◇(B◇(B◇(B◇((((B◇B)◇C)◇C)◇D))))) := congrArg (((B◇B)◇B)◇·) ((l101 B C D).symm)
   _ = (B◇((((B◇B)◇C)◇C)◇D)) := l8 B B ((B◇((((B◇B)◇C)◇C)◇D)))
 have l112 : ∀ (B C D E : G), ((B◇(C◇((D◇(D◇(D◇D)))◇D)))◇E) = ((B◇(C◇D))◇E) := by
  intro B C D E
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46
  clear l47x l47 l48 l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l62 l63 l64 l65 l66x l66 l67
  clear l68 l69 l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l79 l80 l81x l81 l82 l83 l84 l85 l86x
  clear l86 l87x l87 l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l97 l98x l98 l99 l100 l101 l103x l104x l104 l105 l106
  clear l107 l108 l109x l109 l110x l110 l111
  grind
 have l113 : ∀ (B C D : G), ((B◇(C◇((C◇(C◇(C◇C)))◇C)))◇D) = ((B◇(C◇C))◇D) := by
  intro B C D
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l32 l33 l34 l35 l36 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46 l47x
  clear l48 l49x l49 l50x l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67 l69 l70x
  clear l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l78 l79 l80 l81x l81 l82 l83 l85 l86x l86 l87x l87
  clear l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l96 l97 l98x l98 l99 l100 l101 l102 l103x l103 l104x l104 l105 l106
  clear l107 l108 l109x l109 l110x l110 l111 l112
  grind
 have l114x : ∀ (A B C : G), (A◇((A◇(A◇A))◇((A◇(A◇A))◇(((A◇(A◇A))◇(A◇(A◇A)))◇B)))) = (((C◇(A◇A))◇A)◇(A◇(C◇(((A◇(A◇A))◇((A◇(A◇A))◇(A◇(A◇A))))◇B)))) := by
  intro A B C
  calc (A◇((A◇(A◇A))◇((A◇(A◇A))◇(((A◇(A◇A))◇(A◇(A◇A)))◇B))))
   _ = (A◇((((A◇(A◇A))◇C)◇C)◇(C◇(((A◇(A◇A))◇((A◇(A◇A))◇(A◇(A◇A))))◇B)))) := congrArg (A◇·) ((l105 ((A◇(A◇A))) C B).symm)
   _ = (((C◇(A◇A))◇A)◇(A◇(C◇(((A◇(A◇A))◇((A◇(A◇A))◇(A◇(A◇A))))◇B)))) := l104 A C ((C◇(((A◇(A◇A))◇((A◇(A◇A))◇(A◇(A◇A))))◇B)))
 have l114 : ∀ (B C D : G), (((B◇(C◇C))◇C)◇(C◇(B◇((C◇C)◇D)))) = (((C◇C)◇C)◇D) := by
  intro B C D
  have strict_rw_24 := ((l114x C D B).symm)
  rw [l46, l46, l46, l46, l64, l65, l106, l46, l107, l47, l50] at strict_rw_24
  exact strict_rw_24
 have l115 : ∀ (B C D : G), ((B◇(C◇C))◇(C◇(((((C◇(C◇C))◇B)◇B)◇C)◇D))) = D := by
  intro B C D
  calc ((B◇(C◇C))◇(C◇(((((C◇(C◇C))◇B)◇B)◇C)◇D)))
   _ = ((B◇((C◇(C◇C))◇((C◇C)◇C)))◇(C◇(((((C◇(C◇C))◇B)◇B)◇C)◇D))) := (l108 B C C ((C◇(((((C◇(C◇C))◇B)◇B)◇C)◇D)))).symm
   _ = D := l109 B ((C◇(C◇C))) C D
 have l116x : ∀ (A B C : G), ((A◇((((B◇B)◇B)◇((B◇B)◇B))◇(((B◇B)◇(B◇((B◇B)◇B)))◇(((B◇B)◇B)◇((B◇B)◇B)))))◇C) = ((A◇(((B◇B)◇B)◇((B◇B)◇B)))◇C) := by
  intro A B C
  calc ((A◇((((B◇B)◇B)◇((B◇B)◇B))◇(((B◇B)◇(B◇((B◇B)◇B)))◇(((B◇B)◇B)◇((B◇B)◇B)))))◇C)
   _ = ((A◇((((B◇B)◇B)◇((B◇B)◇B))◇(((((B◇B)◇B)◇((B◇B)◇B))◇(((B◇B)◇B)◇((B◇B)◇B)))◇(((B◇B)◇B)◇((B◇B)◇B)))))◇C) := congrArg (·◇C) (congrArg (A◇·) (congrArg ((((B◇B)◇B)◇((B◇B)◇B))◇·) (congrArg (·◇(((B◇B)◇B)◇((B◇B)◇B))) ((l63 B ((B◇B)) (((B◇B)◇B))).symm))))
   _ = ((A◇(((B◇B)◇B)◇((B◇B)◇B)))◇C) := l49 A ((((B◇B)◇B)◇((B◇B)◇B))) C
 have l116 : ∀ (B C D : G), ((B◇((C◇(C◇C))◇C))◇D) = ((B◇(C◇(C◇C)))◇D) := by
  intro B C D
  have strict_rw_25 := (l116x B C D)
  rw [l33, l12, l31, l65, l8] at strict_rw_25
  exact strict_rw_25
 have l117 : ∀ (B C : G), ((B◇((B◇(B◇(B◇B)))◇B))◇C) = ((B◇B)◇C) := by
  intro B C
  calc ((B◇((B◇(B◇(B◇B)))◇B))◇C)
   _ = ((B◇((((B◇B)◇B)◇B)◇B))◇C) := congrArg (·◇C) (congrArg (B◇·) ((l37 B B).symm))
   _ = ((B◇B)◇C) := l24 B B C
 have l118 : ∀ (B C D : G), (((B◇(B◇(C◇B)))◇((B◇B)◇B))◇D) = (((B◇C)◇C)◇D) := by
  intro B C D
  calc (((B◇(B◇(C◇B)))◇((B◇B)◇B))◇D)
   _ = (((B◇(B◇(((((B◇C)◇C)◇B)◇B)◇B)))◇((B◇B)◇B))◇D) := congrArg (·◇D) (congrArg (·◇((B◇B)◇B)) (congrArg (B◇·) (congrArg (B◇·) ((l4 B C B).symm))))
   _ = (((B◇C)◇C)◇D) := l110 B (((B◇C)◇C)) D
 have l119x : ∀ (A B C D : G), (A◇B) = (((C◇(A◇A))◇A)◇(A◇((((((A◇(A◇A))◇C)◇C)◇D)◇D)◇(D◇B)))) := by
  intro A B C D
  calc (A◇B)
   _ = (A◇((((A◇(A◇A))◇C)◇C)◇((((((A◇(A◇A))◇C)◇C)◇D)◇D)◇(D◇B)))) := congrArg (A◇·) ((l5 ((((A◇(A◇A))◇C)◇C)) D B).symm)
   _ = (((C◇(A◇A))◇A)◇(A◇((((((A◇(A◇A))◇C)◇C)◇D)◇D)◇(D◇B)))) := l104 A C (((((((A◇(A◇A))◇C)◇C)◇D)◇D)◇(D◇B)))
 have l119 : ∀ (B C D : G), (((B◇(C◇C))◇C)◇(C◇(B◇((C◇(C◇C))◇D)))) = (C◇D) := by
  intro B C D
  have strict_rw_26 := ((l119x C D B B).symm)
  rw [l6] at strict_rw_26
  exact strict_rw_26
 have l120x : ∀ (A B C D : G), (((A◇A)◇A)◇B) = (A◇((((A◇A)◇C)◇C)◇(((((A◇C)◇C)◇D)◇D)◇(D◇B)))) := by
  intro A B C D
  calc (((A◇A)◇A)◇B)
   _ = (((A◇A)◇A)◇(((A◇C)◇C)◇(((((A◇C)◇C)◇D)◇D)◇(D◇B)))) := congrArg (((A◇A)◇A)◇·) ((l5 (((A◇C)◇C)) D B).symm)
   _ = (A◇((((A◇A)◇C)◇C)◇(((((A◇C)◇C)◇D)◇D)◇(D◇B)))) := l111 A C ((((((A◇C)◇C)◇D)◇D)◇(D◇B)))
 have l120 : ∀ (B C D : G), (B◇((((B◇B)◇C)◇C)◇(C◇(B◇D)))) = (((B◇B)◇B)◇D) := by
  intro B C D
  have strict_rw_27 := ((l120x B D C B).symm)
  rw [l6] at strict_rw_27
  exact strict_rw_27
 have l121 : ∀ (B C D : G), ((B◇(C◇B))◇(B◇D)) = (B◇((C◇(B◇B))◇D)) := by
  intro B C D
  calc ((B◇(C◇B))◇(B◇D))
   _ = ((B◇(C◇((B◇(B◇(B◇B)))◇B)))◇(B◇D)) := (l112 B C B ((B◇D))).symm
   _ = (B◇((C◇((B◇(B◇(B◇B)))◇(B◇B)))◇D)) := l71 B C ((B◇(B◇(B◇B)))) D
   _ = (B◇((C◇(B◇((B◇(B◇(B◇B)))◇B)))◇D)) := congrArg (B◇·) (congrArg (·◇D) (congrArg (C◇·) (((l71 B B B B).symm).symm)))
   _ = (B◇((C◇(B◇B))◇D)) := congrArg (B◇·) (((l112 C B B D).symm).symm)
 have l122x : ∀ (A B C : G), (((A◇((B◇B)◇(B◇B)))◇(B◇B))◇((B◇B)◇(A◇C))) = ((((B◇B)◇(B◇B))◇(B◇B))◇(B◇(((((B◇(B◇B))◇(B◇B))◇(B◇B))◇B)◇C))) := by
  intro A B C
  calc (((A◇((B◇B)◇(B◇B)))◇(B◇B))◇((B◇B)◇(A◇C)))
   _ = (((A◇((B◇B)◇(B◇B)))◇(B◇B))◇((B◇B)◇(A◇(((B◇B)◇(B◇B))◇(B◇(((((B◇(B◇B))◇(B◇B))◇(B◇B))◇B)◇C)))))) := congrArg (((A◇((B◇B)◇(B◇B)))◇(B◇B))◇·) (congrArg ((B◇B)◇·) (congrArg (A◇·) ((l115 ((B◇B)) B C).symm)))
   _ = ((((B◇B)◇(B◇B))◇(B◇B))◇(B◇(((((B◇(B◇B))◇(B◇B))◇(B◇B))◇B)◇C))) := l114 A ((B◇B)) ((B◇(((((B◇(B◇B))◇(B◇B))◇(B◇B))◇B)◇C)))
 have l122 : ∀ (B C D : G), (((B◇C)◇(C◇C))◇((C◇C)◇(B◇D))) = (C◇(C◇((C◇C)◇D))) := by
  intro B C D
  have strict_rw_28 := (l122x B C D)
  rw [l12, l49, l25] at strict_rw_28
  rw (occs := .pos [2]) [l46] at strict_rw_28
  rw [l116, l68, l117] at strict_rw_28
  rw (occs := .pos [1]) [l46] at strict_rw_28
  rw [l106] at strict_rw_28
  exact strict_rw_28
 have l123 : ∀ (B C D : G), ((B◇B)◇((((B◇C)◇C)◇B)◇((C◇B)◇D))) = (B◇(B◇(B◇D))) := by
  intro B C D
  calc ((B◇B)◇((((B◇C)◇C)◇B)◇((C◇B)◇D)))
   _ = (B◇(B◇(B◇(B◇((((B◇C)◇C)◇B)◇((C◇B)◇D)))))) := (l23 B (((((B◇C)◇C)◇B)◇((C◇B)◇D)))).symm
   _ = (B◇(B◇(B◇D))) := congrArg (B◇·) (congrArg (B◇·) (congrArg (B◇·) (l36 B C D)))
 have l124x : ∀ (A B C D : G), (((A◇(A◇(B◇A)))◇((A◇A)◇A))◇(((((A◇B)◇B)◇C)◇C)◇(C◇D))) = D := by
  intro A B C D
  calc (((A◇(A◇(B◇A)))◇((A◇A)◇A))◇(((((A◇B)◇B)◇C)◇C)◇(C◇D)))
   _ = (((A◇B)◇B)◇(((((A◇B)◇B)◇C)◇C)◇(C◇D))) := l118 A B ((((((A◇B)◇B)◇C)◇C)◇(C◇D)))
   _ = D := l5 (((A◇B)◇B)) C D
 have l124 : ∀ (B C D : G), (((B◇(B◇(C◇B)))◇((B◇B)◇B))◇(C◇(B◇D))) = D := by
  intro B C D
  have strict_rw_29 := (l124x B C B D)
  rw [l6] at strict_rw_29
  exact strict_rw_29
 have l125 : ∀ (B C D : G), (B◇(B◇(((((B◇C)◇C)◇B)◇((C◇B)◇B))◇D))) = D := by
  intro B C D
  calc (B◇(B◇(((((B◇C)◇C)◇B)◇((C◇B)◇B))◇D)))
   _ = (B◇(B◇(((((B◇C)◇C)◇B)◇((((((B◇C)◇C)◇B)◇B)◇B)◇B))◇D))) := congrArg (B◇·) (congrArg (B◇·) (congrArg (·◇D) (congrArg ((((B◇C)◇C)◇B)◇·) (congrArg (·◇B) ((l4 B C B).symm)))))
   _ = D := l16 B ((((B◇C)◇C)◇B)) D
 have l126 : ∀ (B C D : G), (((((B◇C)◇C)◇B)◇((C◇B)◇B))◇D) = (((B◇B)◇B)◇D) := by
  intro B C D
  calc (((((B◇C)◇C)◇B)◇((C◇B)◇B))◇D)
   _ = (((((B◇C)◇C)◇B)◇((((((B◇C)◇C)◇B)◇B)◇B)◇B))◇D) := congrArg (·◇D) (congrArg ((((B◇C)◇C)◇B)◇·) (congrArg (·◇B) ((l4 B C B).symm)))
   _ = (((B◇B)◇B)◇D) := l19 ((((B◇C)◇C)◇B)) B D
 have l127x : ∀ (A B C D : G), (((A◇(B◇B))◇B)◇(B◇(A◇((((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B)))◇C)))) = (B◇(((((B◇(B◇B))◇(B◇(B◇B)))◇D)◇D)◇(D◇((B◇(B◇B))◇C)))) := by
  intro A B C D
  calc (((A◇(B◇B))◇B)◇(B◇(A◇((((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B)))◇C))))
   _ = (((A◇(B◇B))◇B)◇(B◇(A◇((B◇(B◇B))◇(((((B◇(B◇B))◇(B◇(B◇B)))◇D)◇D)◇(D◇((B◇(B◇B))◇C))))))) := congrArg (((A◇(B◇B))◇B)◇·) (congrArg (B◇·) (congrArg (A◇·) ((l120 ((B◇(B◇B))) D C).symm)))
   _ = (B◇(((((B◇(B◇B))◇(B◇(B◇B)))◇D)◇D)◇(D◇((B◇(B◇B))◇C)))) := l119 A B ((((((B◇(B◇B))◇(B◇(B◇B)))◇D)◇D)◇(D◇((B◇(B◇B))◇C))))
 have l127 : ∀ (B C D : G), (((B◇(C◇C))◇C)◇(C◇(B◇(C◇D)))) = ((C◇(C◇(C◇C)))◇D) := by
  intro B C D
  have hx := l127x B C D B
  conv at hx =>
   lhs
   rw [l46, l46, l65, l8]
  conv at hx =>
   rhs
   rw [l46, l46, l65, l6, l78]
  exact hx
 have l128x : ∀ (A B C D : G), A = (B◇(C◇((((B◇(C◇D))◇(D◇(B◇(C◇D))))◇(D◇(B◇(C◇D))))◇A))) := by
  intro A B C D
  calc A
   _ = ((D◇(B◇(C◇D)))◇((B◇(C◇D))◇((((B◇(C◇D))◇(D◇(B◇(C◇D))))◇(D◇(B◇(C◇D))))◇A))) := ((l3 A ((D◇(B◇(C◇D)))) ((B◇(C◇D)))).symm).symm
   _ = (B◇(C◇((((B◇(C◇D))◇(D◇(B◇(C◇D))))◇(D◇(B◇(C◇D))))◇A))) := l14 D B C (((((B◇(C◇D))◇(D◇(B◇(C◇D))))◇(D◇(B◇(C◇D))))◇A))
 have l128 : ∀ (B C D E : G), (B◇(C◇(((((B◇(C◇D))◇D)◇D)◇(B◇(C◇D)))◇E))) = E := by
  intro B C D E
  have strict_rw_30 := ((l128x E B C D).symm)
  rw [l40] at strict_rw_30
  exact strict_rw_30
 have l129 : ∀ (B C D E : G), (B◇((C◇(B◇B))◇(D◇(((D◇B)◇B)◇E)))) = ((B◇(C◇B))◇E) := by
  intro B C D E
  calc (B◇((C◇(B◇B))◇(D◇(((D◇B)◇B)◇E))))
   _ = ((B◇(C◇B))◇(B◇(D◇(((D◇B)◇B)◇E)))) := (l121 B C ((D◇(((D◇B)◇B)◇E)))).symm
   _ = ((B◇(C◇B))◇E) := congrArg ((B◇(C◇B))◇·) ((l3 E B D).symm)
 have l130 : ∀ (B C D E : G), (((B◇C)◇C)◇(C◇D)) = ((((B◇E)◇E)◇B)◇((E◇B)◇D)) := by
  intro B C D E
  calc (((B◇C)◇C)◇(C◇D))
   _ = (((B◇C)◇C)◇(C◇(B◇((((B◇E)◇E)◇B)◇((E◇B)◇D))))) := congrArg (((B◇C)◇C)◇·) (congrArg (C◇·) ((l36 B E D).symm))
   _ = ((((B◇E)◇E)◇B)◇((E◇B)◇D)) := l8 B C (((((B◇E)◇E)◇B)◇((E◇B)◇D)))
 have l131 : ∀ (B C D : G), ((B◇B)◇(((B◇C)◇C)◇(C◇D))) = (B◇(B◇(B◇D))) := by
  intro B C D
  calc ((B◇B)◇(((B◇C)◇C)◇(C◇D)))
   _ = ((B◇B)◇(((B◇B)◇B)◇(B◇D))) := congrArg ((B◇B)◇·) ((l53 B B D C).symm)
   _ = (B◇(B◇(B◇D))) := l22 B ((B◇D))
 have l132 : ∀ (B C D : G), ((B◇(C◇C))◇(C◇(C◇(C◇D)))) = (C◇(C◇((C◇C)◇((B◇C)◇D)))) := by
  intro B C D
  calc ((B◇(C◇C))◇(C◇(C◇(C◇D))))
   _ = ((((((C◇B)◇B)◇C)◇C)◇(C◇C))◇(C◇(C◇(C◇D)))) := congrArg (·◇(C◇(C◇(C◇D)))) ((l4 C B ((C◇C))).symm)
   _ = ((((((C◇B)◇B)◇C)◇C)◇(C◇C))◇((C◇C)◇((((C◇B)◇B)◇C)◇((B◇C)◇D)))) := congrArg ((((((C◇B)◇B)◇C)◇C)◇(C◇C))◇·) ((l123 C B D).symm)
   _ = (C◇(C◇((C◇C)◇((B◇C)◇D)))) := l122 ((((C◇B)◇B)◇C)) C (((B◇C)◇D))
 have l133x : ∀ (A B C D : G), (((A◇(A◇(B◇A)))◇((A◇A)◇A))◇(B◇C)) = (A◇(((((A◇D)◇D)◇A)◇((D◇A)◇A))◇C)) := by
  intro A B C D
  calc (((A◇(A◇(B◇A)))◇((A◇A)◇A))◇(B◇C))
   _ = (((A◇(A◇(B◇A)))◇((A◇A)◇A))◇(B◇(A◇(A◇(((((A◇D)◇D)◇A)◇((D◇A)◇A))◇C))))) := congrArg (((A◇(A◇(B◇A)))◇((A◇A)◇A))◇·) (congrArg (B◇·) ((l125 A D C).symm))
   _ = (A◇(((((A◇D)◇D)◇A)◇((D◇A)◇A))◇C)) := l124 A B ((A◇(((((A◇D)◇D)◇A)◇((D◇A)◇A))◇C)))
 have l133 : ∀ (B C D : G), (((B◇(B◇(C◇B)))◇((B◇B)◇B))◇(C◇D)) = (B◇(((B◇B)◇B)◇D)) := by
  intro B C D
  have strict_rw_31 := (l133x B C D B)
  rw [l126] at strict_rw_31
  exact strict_rw_31
 have l134 : ∀ (B C D : G), (((((B◇C)◇C)◇(C◇C))◇C)◇(C◇D)) = ((C◇(C◇(C◇C)))◇(B◇D)) := by
  intro B C D
  calc (((((B◇C)◇C)◇(C◇C))◇C)◇(C◇D))
   _ = (((((B◇C)◇C)◇(C◇C))◇C)◇(C◇(((B◇C)◇C)◇(C◇(B◇D))))) := congrArg (((((B◇C)◇C)◇(C◇C))◇C)◇·) (congrArg (C◇·) ((l8 B C D).symm))
   _ = ((C◇(C◇(C◇C)))◇(B◇D)) := l127 (((B◇C)◇C)) C ((B◇D))
 have l135 : ∀ (B C D E : G), (((((B◇(C◇D))◇D)◇D)◇(B◇(C◇D)))◇E) = (((C◇B)◇B)◇E) := by
  intro B C D E
  calc (((((B◇(C◇D))◇D)◇D)◇(B◇(C◇D)))◇E)
   _ = (((C◇B)◇B)◇(B◇(C◇(((((B◇(C◇D))◇D)◇D)◇(B◇(C◇D)))◇E)))) := (l8 C B ((((((B◇(C◇D))◇D)◇D)◇(B◇(C◇D)))◇E))).symm
   _ = (((C◇B)◇B)◇E) := congrArg (((C◇B)◇B)◇·) (l128 B C D E)
 have l136x : ∀ (A B C D : G), (A◇((B◇(A◇A))◇((A◇A)◇(((A◇C)◇C)◇(C◇D))))) = ((A◇(B◇A))◇((A◇A)◇D)) := by
  intro A B C D
  calc (A◇((B◇(A◇A))◇((A◇A)◇(((A◇C)◇C)◇(C◇D)))))
   _ = (A◇((B◇(A◇A))◇((A◇A)◇((((A◇A)◇A)◇A)◇((A◇A)◇D))))) := congrArg (A◇·) (congrArg ((B◇(A◇A))◇·) (congrArg ((A◇A)◇·) (((l130 A C D A).symm).symm)))
   _ = ((A◇(B◇A))◇((A◇A)◇D)) := l129 A B ((A◇A)) (((A◇A)◇D))
 have l136 : ∀ (B C D : G), ((B◇(B◇B))◇((C◇B)◇D)) = ((B◇(C◇B))◇((B◇B)◇D)) := by
  intro B C D
  have strict_rw_32 := (l136x B C B D)
  rw [l131, l132, l96] at strict_rw_32
  exact strict_rw_32
 have l137x : ∀ (A B C : G), (((((A◇A)◇A)◇(((A◇A)◇A)◇(B◇((A◇A)◇A))))◇((A◇(A◇A))◇((A◇A)◇A)))◇(B◇C)) = (((A◇A)◇A)◇(((((A◇A)◇A)◇((A◇A)◇A))◇((A◇A)◇A))◇C)) := by
  intro A B C
  calc (((((A◇A)◇A)◇(((A◇A)◇A)◇(B◇((A◇A)◇A))))◇((A◇(A◇A))◇((A◇A)◇A)))◇(B◇C))
   _ = (((((A◇A)◇A)◇(((A◇A)◇A)◇(B◇((A◇A)◇A))))◇((((A◇A)◇A)◇((A◇A)◇A))◇((A◇A)◇A)))◇(B◇C)) := congrArg (·◇(B◇C)) (congrArg ((((A◇A)◇A)◇(((A◇A)◇A)◇(B◇((A◇A)◇A))))◇·) (congrArg (·◇((A◇A)◇A)) ((l33 A A).symm)))
   _ = (((A◇A)◇A)◇(((((A◇A)◇A)◇((A◇A)◇A))◇((A◇A)◇A))◇C)) := l133 (((A◇A)◇A)) B C
 have l137 : ∀ (B C D : G), ((B◇(((B◇(B◇(B◇B)))◇(C◇B))◇B))◇(C◇D)) = (B◇(B◇D)) := by
  intro B C D
  have hx := (l137x B C D)
  rw [l111, l37, l107, l47, l85, l12, l61, l112] at hx
  exact hx.trans (by rw [← l7, l20, l22, l7]; grind)
 have l138 : ∀ (B C D E : G), ((B◇(B◇(B◇B)))◇(((C◇D)◇D)◇E)) = (((D◇(C◇B))◇B)◇(B◇E)) := by
  intro B C D E
  calc ((B◇(B◇(B◇B)))◇(((C◇D)◇D)◇E))
   _ = (((((((C◇D)◇D)◇B)◇B)◇(B◇B))◇B)◇(B◇E)) := (l134 (((C◇D)◇D)) B E).symm
   _ = (((D◇(C◇B))◇B)◇(B◇E)) := congrArg (·◇(B◇E)) (congrArg (·◇B) (l6 C D B B))
 have l139 : ∀ (B C D : G), (((B◇B)◇(C◇(B◇B)))◇(B◇D)) = (((B◇B)◇B)◇((C◇(B◇B))◇D)) := by
  intro B C D
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l24x l24
  clear l26 l27 l28 l29 l30 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46 l47x l47
  clear l48 l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67 l68
  clear l69 l70x l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l78 l79 l80 l81x l81 l82 l83 l84 l85 l86x l86
  clear l87x l87 l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l96 l97 l98x l98 l99 l100 l101 l102 l103x l103 l104x l104
  clear l105 l106 l107 l108 l109x l109 l110x l110 l111 l112 l113 l114x l114 l115 l116x l116 l117 l118 l119x l119 l120x l120 l121 l122x
  clear l122 l123 l124x l124 l125 l126 l127 l128x l128 l129 l130 l131 l132 l133x l133 l134 l135 l136x l137x l137 l138
  grind
 have l140 : ∀ (B C D : G), (((B◇((B◇B)◇C))◇(B◇C))◇((B◇C)◇((B◇B)◇D))) = D := by
  intro B C D
  calc (((B◇((B◇B)◇C))◇(B◇C))◇((B◇C)◇((B◇B)◇D)))
   _ = ((((B◇B)◇(B◇C))◇(B◇C))◇((B◇C)◇((B◇B)◇D))) := congrArg (·◇((B◇C)◇((B◇B)◇D))) (congrArg (·◇(B◇C)) ((l12 B C).symm))
   _ = D := l8 ((B◇B)) ((B◇C)) D
 have l141x : ∀ (A B C D : G), ((A◇(((A◇(A◇(A◇A)))◇(((B◇C)◇C)◇A))◇A))◇D) = (A◇(A◇(C◇(B◇D)))) := by
  intro A B C D
  calc ((A◇(((A◇(A◇(A◇A)))◇(((B◇C)◇C)◇A))◇A))◇D)
   _ = ((A◇(((A◇(A◇(A◇A)))◇(((B◇C)◇C)◇A))◇A))◇(((B◇C)◇C)◇(C◇(B◇D)))) := congrArg ((A◇(((A◇(A◇(A◇A)))◇(((B◇C)◇C)◇A))◇A))◇·) ((l8 B C D).symm)
   _ = (A◇(A◇(C◇(B◇D)))) := l137 A (((B◇C)◇C)) ((C◇(B◇D)))
 have l141 : ∀ (B C D E : G), ((B◇((((C◇(D◇B))◇B)◇(B◇B))◇B))◇E) = (B◇(B◇(C◇(D◇E)))) := by
  intro B C D E
  have strict_rw_33 := (l141x B D C E)
  rw [l138] at strict_rw_33
  exact strict_rw_33
 have l142 : ∀ (B C D : G), ((((((B◇B)◇C)◇C)◇B)◇B)◇D) = (C◇(B◇(B◇(B◇D)))) := by
  intro B C D
  calc ((((((B◇B)◇C)◇C)◇B)◇B)◇D)
   _ = (C◇((B◇B)◇((((B◇B)◇C)◇C)◇((((((B◇B)◇C)◇C)◇B)◇B)◇D)))) := ((l3 (((((((B◇B)◇C)◇C)◇B)◇B)◇D)) C ((B◇B))).symm).symm
   _ = (C◇(B◇(B◇(B◇D)))) := congrArg (C◇·) (l43 B ((((B◇B)◇C)◇C)) D)
 have l143 : ∀ (B C D E : G), (((B◇B)◇(C◇(D◇B)))◇(B◇E)) = (((B◇B)◇B)◇((C◇(D◇B))◇E)) := by
  intro B C D E
  calc (((B◇B)◇(C◇(D◇B)))◇(B◇E))
   _ = (((B◇B)◇(((((D◇C)◇C)◇B)◇B)◇(B◇B)))◇(B◇E)) := congrArg (·◇(B◇E)) (congrArg ((B◇B)◇·) ((l6 D C B B).symm))
   _ = (((B◇B)◇B)◇((((((D◇C)◇C)◇B)◇B)◇(B◇B))◇E)) := l139 B (((((D◇C)◇C)◇B)◇B)) E
   _ = (((B◇B)◇B)◇((C◇(D◇B))◇E)) := congrArg (((B◇B)◇B)◇·) (congrArg (·◇E) (((l6 D C B B).symm).symm))
 have l144 : ∀ (B C D E : G), (B◇((((B◇C)◇C)◇B)◇D)) = ((((C◇B)◇E)◇E)◇(E◇D)) := by
  intro B C D E
  calc (B◇((((B◇C)◇C)◇B)◇D))
   _ = (B◇((((B◇C)◇C)◇B)◇((C◇B)◇((((C◇B)◇E)◇E)◇(E◇D))))) := congrArg (B◇·) (congrArg ((((B◇C)◇C)◇B)◇·) ((l5 ((C◇B)) E D).symm))
   _ = ((((C◇B)◇E)◇E)◇(E◇D)) := l36 B C (((((C◇B)◇E)◇E)◇(E◇D)))
 have l145 : ∀ (B C D E : G), (B◇(((C◇(D◇B))◇B)◇(B◇(C◇(D◇((B◇B)◇E)))))) = E := by
  intro B C D E
  grind
 have l146 : ∀ (B C D : G), ((B◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇(B◇D))) = D := by
  intro B C D
  calc ((B◇B)◇(((((B◇C)◇C)◇(C◇B))◇B)◇(B◇D)))
   _ = ((B◇B)◇((((B◇B)◇B)◇B)◇(B◇D))) := congrArg ((B◇B)◇·) (congrArg (·◇(B◇D)) ((l57 B B C).symm))
   _ = D := l5 ((B◇B)) B D
 have l147 : ∀ (B C D : G), (((B◇B)◇B)◇((B◇(C◇B))◇D)) = (B◇(((B◇B)◇(C◇(B◇B)))◇D)) := by
  intro B C D
  calc (((B◇B)◇B)◇((B◇(C◇B))◇D))
   _ = (((B◇B)◇(B◇(C◇B)))◇(B◇D)) := (l143 B B C D).symm
   _ = ((B◇((B◇B)◇(C◇B)))◇(B◇D)) := congrArg (·◇(B◇D)) (l12 B ((C◇B)))
   _ = (B◇(((B◇B)◇(C◇(B◇B)))◇D)) := ((l71 B ((B◇B)) C D).symm).symm
 have l148 : ∀ (B C : G), ((B◇(B◇B))◇((B◇(B◇(B◇B)))◇C)) = (B◇(B◇C)) := by
  intro B C
  calc ((B◇(B◇B))◇((B◇(B◇(B◇B)))◇C))
   _ = (B◇(B◇(B◇((B◇B)◇((B◇(B◇(B◇B)))◇C))))) := (l96 B (((B◇(B◇(B◇B)))◇C))).symm
   _ = (B◇(B◇(B◇((B◇B)◇((((B◇B)◇B)◇B)◇C))))) := congrArg (B◇·) (congrArg (B◇·) (congrArg (B◇·) (congrArg ((B◇B)◇·) ((l37 B C).symm))))
   _ = (B◇(B◇C)) := congrArg (B◇·) (congrArg (B◇·) ((l3 C B ((B◇B))).symm))
 have l149 : ∀ (B C D : G), (B◇(C◇(B◇((B◇(C◇B))◇(C◇((B◇B)◇D)))))) = D := by
  intro B C D
  calc (B◇(C◇(B◇((B◇(C◇B))◇(C◇((B◇B)◇D))))))
   _ = (((((C◇B)◇B)◇B)◇B)◇(B◇(B◇((B◇(C◇B))◇(C◇((B◇B)◇D)))))) := (l6 C B B ((B◇((B◇(C◇B))◇(C◇((B◇B)◇D)))))).symm
   _ = (B◇((((B◇(C◇B))◇(C◇B))◇B)◇(B◇((B◇(C◇B))◇(C◇((B◇B)◇D)))))) := (l144 B ((C◇B)) ((B◇((B◇(C◇B))◇(C◇((B◇B)◇D))))) B).symm
   _ = D := l145 B ((B◇(C◇B))) C D
 have l150x : ∀ (A B C D : G), ((((A◇A)◇A)◇((A◇A)◇A))◇(((((((A◇A)◇A)◇B)◇B)◇(B◇((A◇A)◇A)))◇((A◇A)◇A))◇(A◇(((A◇A)◇(C◇(A◇A)))◇D)))) = ((A◇(C◇A))◇D) := by
  intro A B C D
  calc ((((A◇A)◇A)◇((A◇A)◇A))◇(((((((A◇A)◇A)◇B)◇B)◇(B◇((A◇A)◇A)))◇((A◇A)◇A))◇(A◇(((A◇A)◇(C◇(A◇A)))◇D))))
   _ = ((((A◇A)◇A)◇((A◇A)◇A))◇(((((((A◇A)◇A)◇B)◇B)◇(B◇((A◇A)◇A)))◇((A◇A)◇A))◇(((A◇A)◇A)◇((A◇(C◇A))◇D)))) := congrArg ((((A◇A)◇A)◇((A◇A)◇A))◇·) (congrArg (((((((A◇A)◇A)◇B)◇B)◇(B◇((A◇A)◇A)))◇((A◇A)◇A))◇·) ((l147 A C D).symm))
   _ = ((A◇(C◇A))◇D) := l146 (((A◇A)◇A)) B (((A◇(C◇A))◇D))
 have l150 : ∀ (B C D : G), (B◇(B◇(B◇(((B◇B)◇(C◇(B◇B)))◇D)))) = ((B◇(C◇B))◇D) := by
  intro B C D
  have strict_rw_34 := (l150x B B C D)
  rw [l20, l22, l6, l103, l23, l31] at strict_rw_34
  rw (occs := .pos [1]) [l121] at strict_rw_34
  rw (occs := .pos [2]) [l121] at strict_rw_34
  rw [l116] at strict_rw_34
  rw (occs := .pos [1]) [l121] at strict_rw_34
  rw [l148] at strict_rw_34
  exact strict_rw_34
 have l151 : ∀ (B C : G), ((B◇(B◇B))◇((B◇(B◇B))◇C)) = (((B◇B)◇B)◇(B◇C)) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l9 l10 l11 l12 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l32 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46 l47x
  clear l47 l48 l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x l66 l67
  clear l68 l69 l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l78 l79 l80 l81x l81 l82 l83 l84 l85
  clear l86x l86 l87x l87 l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l96 l97 l98x l98 l99 l100 l101 l102 l103x l103
  clear l104x l104 l105 l106 l107 l108 l109x l109 l110x l110 l111 l112 l113 l114x l114 l115 l116x l116 l117 l118 l119x l119 l120x l120
  clear l121 l122x l122 l123 l124x l124 l125 l126 l127 l128x l128 l129 l130 l131 l132 l133x l133 l134 l135 l136x l136 l137x l137 l138
  clear l139 l140 l141x l141 l142 l143 l144 l145 l146 l147 l148 l149 l150x l150
  grind
 have l152 : ∀ (B C D : G), (B◇(C◇(B◇((B◇(C◇B))◇D)))) = ((((B◇B)◇C)◇C)◇D) := by
  intro B C D
  calc (B◇(C◇(B◇((B◇(C◇B))◇D))))
   _ = (B◇(C◇(B◇((B◇(C◇B))◇(C◇((B◇B)◇((((B◇B)◇C)◇C)◇D))))))) := congrArg (B◇·) (congrArg (C◇·) (congrArg (B◇·) (congrArg ((B◇(C◇B))◇·) (((l3 D C ((B◇B))).symm).symm))))
   _ = ((((B◇B)◇C)◇C)◇D) := l149 B C (((((B◇B)◇C)◇C)◇D))
 have l153x : ∀ (A B C D E : G), ((A◇(B◇((C◇C)◇((((((C◇C)◇D)◇D)◇(D◇C))◇((((C◇C)◇D)◇D)◇(D◇C)))◇((((C◇C)◇D)◇D)◇(D◇C))))))◇E) = ((A◇(B◇((((C◇C)◇D)◇D)◇(D◇C))))◇E) := by
  intro A B C D E
  calc ((A◇(B◇((C◇C)◇((((((C◇C)◇D)◇D)◇(D◇C))◇((((C◇C)◇D)◇D)◇(D◇C)))◇((((C◇C)◇D)◇D)◇(D◇C))))))◇E)
   _ = ((A◇(B◇(((((C◇C)◇D)◇D)◇(D◇C))◇((((((C◇C)◇D)◇D)◇(D◇C))◇((((C◇C)◇D)◇D)◇(D◇C)))◇((((C◇C)◇D)◇D)◇(D◇C))))))◇E) := congrArg (·◇E) (congrArg (A◇·) (congrArg (B◇·) ((l83 C D (((((((C◇C)◇D)◇D)◇(D◇C))◇((((C◇C)◇D)◇D)◇(D◇C)))◇((((C◇C)◇D)◇D)◇(D◇C))))).symm)))
   _ = ((A◇(B◇((((C◇C)◇D)◇D)◇(D◇C))))◇E) := l61 A B (((((C◇C)◇D)◇D)◇(D◇C))) E
 have l153 : ∀ (B C D E F : G), ((B◇(C◇((((D◇D)◇E)◇E)◇(E◇D))))◇F) = ((B◇(C◇(D◇D)))◇F) := by
  intro B C D E F
  have strict_rw_35 := ((l153x B C D E F).symm)
  rw [l83, l5, l12, l5] at strict_rw_35
  exact strict_rw_35
 have l154 : ∀ (B C D : G), ((B◇B)◇(((B◇B)◇(C◇(B◇B)))◇D)) = (B◇((B◇(C◇B))◇D)) := by
  intro B C D
  clear h l3 l4 l6 l7 l8 l9 l10 l11 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x l24
  clear l26 l27 l28 l29 l30 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45 l46 l47x l47
  clear l48 l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l62 l63 l64 l65 l66x l66 l67 l68 l69
  clear l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l78 l79 l80 l81x l81 l82 l83 l84 l85 l86x l86
  clear l87x l87 l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l96 l97 l98x l98 l99 l100 l101 l102 l103x l103 l104x l104
  clear l105 l106 l107 l108 l109x l109 l110x l110 l111 l112 l113 l114x l114 l115 l116x l116 l117 l118 l119x l119 l120x l120 l122x l122
  clear l123 l124x l124 l125 l126 l127 l128x l128 l129 l130 l131 l132 l133x l133 l134 l135 l136x l136 l137x l137 l138 l139 l140 l141x
  clear l141 l142 l143 l144 l145 l146 l147 l148 l149 l150x l152 l153x l153
  grind
 have l155x : ∀ (A B C D : G), ((A◇A)◇(B◇(((((A◇A)◇C)◇C)◇(C◇A))◇((((((A◇A)◇C)◇C)◇(C◇A))◇(B◇((((A◇A)◇C)◇C)◇(C◇A))))◇D)))) = ((((((((A◇A)◇C)◇C)◇(C◇A))◇((((A◇A)◇C)◇C)◇(C◇A)))◇B)◇B)◇D) := by
  intro A B C D
  calc ((A◇A)◇(B◇(((((A◇A)◇C)◇C)◇(C◇A))◇((((((A◇A)◇C)◇C)◇(C◇A))◇(B◇((((A◇A)◇C)◇C)◇(C◇A))))◇D))))
   _ = (((((A◇A)◇C)◇C)◇(C◇A))◇(B◇(((((A◇A)◇C)◇C)◇(C◇A))◇((((((A◇A)◇C)◇C)◇(C◇A))◇(B◇((((A◇A)◇C)◇C)◇(C◇A))))◇D)))) := (l83 A C ((B◇(((((A◇A)◇C)◇C)◇(C◇A))◇((((((A◇A)◇C)◇C)◇(C◇A))◇(B◇((((A◇A)◇C)◇C)◇(C◇A))))◇D))))).symm
   _ = ((((((((A◇A)◇C)◇C)◇(C◇A))◇((((A◇A)◇C)◇C)◇(C◇A)))◇B)◇B)◇D) := l152 (((((A◇A)◇C)◇C)◇(C◇A))) B D
 have l155 : ∀ (B C D : G), ((B◇B)◇(C◇(B◇((B◇(C◇B))◇D)))) = (((B◇C)◇C)◇D) := by
  intro B C D
  have strict_rw_36 := (l155x B C B D)
  rw [l83, l153, l83, l154, l83, l5] at strict_rw_36
  exact strict_rw_36
 have l156 : ∀ (B C D E F : G), (((B◇(((B◇C)◇C)◇(((D◇E)◇E)◇(E◇C))))◇C)◇F) = (D◇F) := by
  intro B C D E F
  clear h l3 l4 l6 l7 l8 l9 l10 l11 l12 l13 l14x l14 l15 l16x l16 l17 l18 l19 l20 l21 l22 l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41x l41 l42 l43 l44x l44 l45
  clear l46 l47x l47 l48 l49x l49 l50x l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66x
  clear l66 l67 l68 l69 l70x l70 l71 l72 l73 l74x l74 l75x l75 l76x l76 l77 l78x l78 l79 l80 l81x l81 l82 l83
  clear l84 l85 l86x l86 l87x l87 l88 l89x l89 l90 l91 l92x l92 l93 l94 l95 l96 l97 l98x l98 l100 l101 l102 l103x
  clear l103 l104x l104 l105 l106 l107 l108 l109x l109 l110x l110 l111 l112 l113 l114x l114 l115 l116x l116 l117 l118 l119x l119 l120x
  clear l120 l121 l122x l122 l123 l124x l124 l125 l126 l127 l128x l128 l129 l130 l131 l132 l133x l133 l134 l135 l136x l136 l137x l137
  clear l138 l139 l140 l141x l141 l142 l143 l144 l145 l146 l147 l148 l149 l150x l150 l151 l152 l153x l153 l154 l155x l155
  grind
 have l157 : ∀ (B C D : G), (((B◇C)◇C)◇((((B◇(C◇B))◇B)◇B)◇D)) = ((B◇B)◇(C◇D)) := by
  intro B C D
  calc (((B◇C)◇C)◇((((B◇(C◇B))◇B)◇B)◇D))
   _ = ((B◇B)◇(C◇(B◇((B◇(C◇B))◇((((B◇(C◇B))◇B)◇B)◇D))))) := (l155 B C (((((B◇(C◇B))◇B)◇B)◇D))).symm
   _ = ((B◇B)◇(C◇D)) := congrArg ((B◇B)◇·) (congrArg (C◇·) ((l3 D B ((B◇(C◇B)))).symm))
 have l158 : ∀ (B C D : G), (((B◇((B◇B)◇(C◇(B◇C))))◇C)◇D) = ((B◇(C◇B))◇D) := by
  intro B C D
  calc (((B◇((B◇B)◇(C◇(B◇C))))◇C)◇D)
   _ = (((B◇(((B◇C)◇C)◇((((B◇(C◇B))◇B)◇B)◇(B◇C))))◇C)◇D) := congrArg (·◇D) (congrArg (·◇C) (congrArg (B◇·) ((l157 B C ((B◇C))).symm)))
   _ = ((B◇(C◇B))◇D) := l156 B C ((B◇(C◇B))) B D
 have l160x : ∀ (A B C D : G), (((A◇((((((B◇A)◇A)◇B)◇B)◇((((B◇A)◇A)◇B)◇B))◇(C◇(((((B◇A)◇A)◇B)◇B)◇C))))◇C)◇D) = ((((((B◇A)◇A)◇B)◇B)◇(C◇((((B◇A)◇A)◇B)◇B)))◇D) := by
  intro A B C D
  calc (((A◇((((((B◇A)◇A)◇B)◇B)◇((((B◇A)◇A)◇B)◇B))◇(C◇(((((B◇A)◇A)◇B)◇B)◇C))))◇C)◇D)
   _ = (((((((B◇A)◇A)◇B)◇B)◇((((((B◇A)◇A)◇B)◇B)◇((((B◇A)◇A)◇B)◇B))◇(C◇(((((B◇A)◇A)◇B)◇B)◇C))))◇C)◇D) := congrArg (·◇D) (congrArg (·◇C) ((l4 B A (((((((B◇A)◇A)◇B)◇B)◇((((B◇A)◇A)◇B)◇B))◇(C◇(((((B◇A)◇A)◇B)◇B)◇C))))).symm))
   _ = ((((((B◇A)◇A)◇B)◇B)◇(C◇((((B◇A)◇A)◇B)◇B)))◇D) := l158 (((((B◇A)◇A)◇B)◇B)) C D
 have l160 : ∀ (B C D E : G), ((B◇(C◇((((D◇B)◇B)◇D)◇D)))◇E) = ((B◇(C◇B))◇E) := by
  intro B C D E
  have strict_rw_37 := ((l160x B D C E).symm)
  rw [l4, l4, l4, l24, l158] at strict_rw_37
  exact strict_rw_37
 have l162 : ∀ (B C D E F : G), ((B◇(C◇((((D◇E)◇E)◇D)◇D)))◇F) = ((B◇(C◇E))◇F) := by
  intro B C D E F
  calc ((B◇(C◇((((D◇E)◇E)◇D)◇D)))◇F)
   _ = ((E◇(((E◇((C◇B)◇B))◇((C◇B)◇B))◇((((D◇E)◇E)◇D)◇D)))◇F) := congrArg (·◇F) ((l67 E C B (((((D◇E)◇E)◇D)◇D))).symm)
   _ = ((E◇(((E◇((C◇B)◇B))◇((C◇B)◇B))◇E))◇F) := l160 E (((E◇((C◇B)◇B))◇((C◇B)◇B))) D F
   _ = ((B◇(C◇E))◇F) := congrArg (·◇F) (((l67 E C B E).symm).symm)
 have l164x : ∀ (A B C D : G), (A◇B) = ((((((((C◇A)◇D)◇D)◇(C◇A))◇(C◇A))◇A)◇(A◇D))◇B) := by
  intro A B C D
  calc (A◇B)
   _ = ((((((((C◇A)◇D)◇D)◇(C◇A))◇(C◇A))◇A)◇(A◇(((((C◇A)◇D)◇D)◇(C◇A))◇(C◇A))))◇B) := (l9 (((((C◇A)◇D)◇D)◇(C◇A))) C A B).symm
   _ = ((((((((C◇A)◇D)◇D)◇(C◇A))◇(C◇A))◇A)◇(A◇D))◇B) := l162 (((((((C◇A)◇D)◇D)◇(C◇A))◇(C◇A))◇A)) A ((C◇A)) D B
 have l164 : ∀ (B C D : G), (((B◇C)◇(C◇B))◇D) = (C◇D) := by
  intro B C D
  have strict_rw_38 := ((l164x C D B B).symm)
  rw [l4] at strict_rw_38
  exact strict_rw_38
 exact (l164 z x y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8883_to_51690 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8883_to_51690
