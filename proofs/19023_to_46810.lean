-- Equation19023 → Equation46810
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
-- Conclusion: x ◇ x = (x ◇ y) ◇ ((x ◇ y) ◇ y)
-- Original submission SHA-256: 91f5cd7c1172f9717b43f48ace17ccd5563091c58fb080782dbd474c371a1f25
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (x ◇ y) ◇ ((x ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
def submission : Goal := by
 intro G _ h
 intro x y
 have l3 : ∀ (B C D : G), B = ((C◇B)◇((D◇C)◇(B◇D))) := by
  intro B C D
  exact h B C D
 have l4 : ∀ (B C : G), ((B◇(C◇(B◇C)))◇B) = (C◇(B◇C)) := by
  intro B C
  calc ((B◇(C◇(B◇C)))◇B)
   _ = ((B◇(C◇(B◇C)))◇(((B◇C)◇B)◇((C◇(B◇C))◇(B◇C)))) := congrArg ((B◇(C◇(B◇C)))◇·) (((l3 B ((B◇C)) C).symm).symm)
   _ = (C◇(B◇C)) := (l3 ((C◇(B◇C))) B ((B◇C))).symm
 have l5 : ∀ (B : G), (((B◇B)◇B)◇(B◇B)) = B := by
  intro B
  calc (((B◇B)◇B)◇(B◇B))
   _ = (((B◇B)◇((B◇B)◇((B◇B)◇(B◇B))))◇(B◇B)) := congrArg (·◇(B◇B)) (congrArg ((B◇B)◇·) (l3 B B B))
   _ = ((B◇B)◇((B◇B)◇(B◇B))) := l4 ((B◇B)) ((B◇B))
   _ = B := (l3 B B B).symm
 have l6 : ∀ (B C D E : G), ((((B◇C)◇(D◇B))◇E)◇(D◇(E◇(C◇D)))) = E := by
  intro B C D E
  calc ((((B◇C)◇(D◇B))◇E)◇(D◇(E◇(C◇D))))
   _ = ((((B◇C)◇(D◇B))◇E)◇(((C◇D)◇((B◇C)◇(D◇B)))◇(E◇(C◇D)))) := congrArg ((((B◇C)◇(D◇B))◇E)◇·) (congrArg (·◇(E◇(C◇D))) (((l3 D C B).symm).symm))
   _ = E := (l3 E (((B◇C)◇(D◇B))) ((C◇D))).symm
 have l7 : ∀ (B C : G), (((B◇B)◇C)◇(B◇(C◇((B◇B)◇B)))) = C := by
  intro B C
  calc (((B◇B)◇C)◇(B◇(C◇((B◇B)◇B))))
   _ = (((B◇B)◇C)◇((((B◇B)◇B)◇(B◇B))◇(C◇((B◇B)◇B)))) := congrArg (((B◇B)◇C)◇·) (congrArg (·◇(C◇((B◇B)◇B))) ((l5 B).symm))
   _ = C := (l3 C ((B◇B)) (((B◇B)◇B))).symm
 have l8 : ∀ (B C : G), ((((B◇C)◇(((C◇C)◇C)◇B))◇C)◇C) = C := by
  intro B C
  calc ((((B◇C)◇(((C◇C)◇C)◇B))◇C)◇C)
   _ = ((((B◇C)◇(((C◇C)◇C)◇B))◇C)◇(((C◇C)◇C)◇(C◇(C◇((C◇C)◇C))))) := congrArg ((((B◇C)◇(((C◇C)◇C)◇B))◇C)◇·) ((l7 C C).symm)
   _ = C := l6 B C (((C◇C)◇C)) C
 have l9 : ∀ (B : G), (((((B◇B)◇B)◇B)◇B)◇B) = B := by
  intro B
  calc (((((B◇B)◇B)◇B)◇B)◇B)
   _ = (((((B◇B)◇B)◇(((B◇B)◇B)◇(B◇B)))◇B)◇B) := congrArg (·◇B) (congrArg (·◇B) (congrArg (((B◇B)◇B)◇·) ((l5 B).symm)))
   _ = B := l8 ((B◇B)) B
 have l10 : ∀ (B : G), ((((B◇B)◇B)◇((B◇B)◇B))◇((B◇B)◇B)) = ((B◇B)◇B) := by
  intro B
  calc ((((B◇B)◇B)◇((B◇B)◇B))◇((B◇B)◇B))
   _ = ((((B◇B)◇B)◇((B◇B)◇(((B◇B)◇B)◇(B◇B))))◇((B◇B)◇B)) := congrArg (·◇((B◇B)◇B)) (congrArg (((B◇B)◇B)◇·) (congrArg ((B◇B)◇·) ((l5 B).symm)))
   _ = ((B◇B)◇(((B◇B)◇B)◇(B◇B))) := l4 (((B◇B)◇B)) ((B◇B))
   _ = ((B◇B)◇B) := congrArg ((B◇B)◇·) (((l5 B).symm).symm)
 have l11 : ∀ (B C D E : G), ((B◇(C◇D))◇((((E◇C)◇(D◇E))◇B)◇D)) = (C◇D) := by
  intro B C D E
  calc ((B◇(C◇D))◇((((E◇C)◇(D◇E))◇B)◇D))
   _ = ((B◇(C◇D))◇((((E◇C)◇(D◇E))◇B)◇((C◇D)◇((E◇C)◇(D◇E))))) := congrArg ((B◇(C◇D))◇·) (congrArg ((((E◇C)◇(D◇E))◇B)◇·) (((l3 D C E).symm).symm))
   _ = (C◇D) := (l3 ((C◇D)) B (((E◇C)◇(D◇E)))).symm
 have l12 : ∀ (B C : G), ((B◇((C◇C)◇C))◇(((C◇C)◇B)◇C)) = ((C◇C)◇C) := by
  intro B C
  calc ((B◇((C◇C)◇C))◇(((C◇C)◇B)◇C))
   _ = ((B◇((C◇C)◇C))◇(((C◇C)◇B)◇(((C◇C)◇C)◇(C◇C)))) := congrArg ((B◇((C◇C)◇C))◇·) (congrArg (((C◇C)◇B)◇·) ((l5 C).symm))
   _ = ((C◇C)◇C) := (l3 (((C◇C)◇C)) B ((C◇C))).symm
 have l13 : ∀ (B : G), (((B◇B)◇B)◇((B◇B)◇B)) = ((B◇B)◇B) := by
  intro B
  calc (((B◇B)◇B)◇((B◇B)◇B))
   _ = (((((B◇B)◇B)◇((B◇B)◇B))◇((B◇B)◇B))◇((B◇B)◇B)) := congrArg (·◇((B◇B)◇B)) ((l10 B).symm)
   _ = (((((((B◇B)◇B)◇((B◇B)◇B))◇((B◇B)◇B))◇((B◇B)◇B))◇((B◇B)◇B))◇((B◇B)◇B)) := congrArg (·◇((B◇B)◇B)) (congrArg (·◇((B◇B)◇B)) (congrArg (·◇((B◇B)◇B)) ((l10 B).symm)))
   _ = ((B◇B)◇B) := ((l9 (((B◇B)◇B))).symm).symm
 have l14 : ∀ (B C : G), (((B◇((C◇B)◇((B◇B)◇B)))◇(B◇C))◇((C◇B)◇C)) = (B◇C) := by
  intro B C
  calc (((B◇((C◇B)◇((B◇B)◇B)))◇(B◇C))◇((C◇B)◇C))
   _ = (((B◇((C◇B)◇((B◇B)◇B)))◇(B◇C))◇((((B◇B)◇(C◇B))◇(B◇((C◇B)◇((B◇B)◇B))))◇C)) := congrArg (((B◇((C◇B)◇((B◇B)◇B)))◇(B◇C))◇·) (congrArg (·◇C) ((l7 B ((C◇B))).symm))
   _ = (B◇C) := l11 ((B◇((C◇B)◇((B◇B)◇B)))) B C B
 have l15 : ∀ (B : G), (((B◇B)◇B)◇(((B◇B)◇((B◇B)◇B))◇B)) = ((B◇B)◇B) := by
  intro B
  calc (((B◇B)◇B)◇(((B◇B)◇((B◇B)◇B))◇B))
   _ = ((((B◇B)◇B)◇((B◇B)◇B))◇(((B◇B)◇((B◇B)◇B))◇B)) := congrArg (·◇(((B◇B)◇((B◇B)◇B))◇B)) ((l13 B).symm)
   _ = ((B◇B)◇B) := l12 (((B◇B)◇B)) B
 have l16 : ∀ (B : G), ((B◇B)◇(B◇((B◇B)◇B))) = ((B◇B)◇B) := by
  intro B
  calc ((B◇B)◇(B◇((B◇B)◇B)))
   _ = ((((B◇((B◇B)◇((B◇B)◇B)))◇(B◇B))◇((B◇B)◇B))◇(B◇((B◇B)◇B))) := congrArg (·◇(B◇((B◇B)◇B))) ((l14 B B).symm)
   _ = ((((B◇((B◇B)◇((B◇B)◇B)))◇(B◇B))◇((B◇B)◇B))◇(B◇(((B◇B)◇B)◇(((B◇B)◇((B◇B)◇B))◇B)))) := congrArg ((((B◇((B◇B)◇((B◇B)◇B)))◇(B◇B))◇((B◇B)◇B))◇·) (congrArg (B◇·) ((l15 B).symm))
   _ = ((B◇B)◇B) := l6 B (((B◇B)◇((B◇B)◇B))) B (((B◇B)◇B))
 have l17 : ∀ (B : G), (B◇((B◇B)◇B)) = B := by
  intro B
  calc (B◇((B◇B)◇B))
   _ = (((B◇B)◇(B◇((B◇B)◇B)))◇(B◇B)) := (l4 ((B◇B)) B).symm
   _ = (((B◇B)◇B)◇(B◇B)) := congrArg (·◇(B◇B)) (l16 B)
   _ = B := ((l5 B).symm).symm
 have l18 : ∀ (B C D : G), ((B◇(C◇B))◇((D◇(C◇(B◇(C◇B))))◇(C◇D))) = C := by
  intro B C D
  calc ((B◇(C◇B))◇((D◇(C◇(B◇(C◇B))))◇(C◇D)))
   _ = (((C◇(B◇(C◇B)))◇C)◇((D◇(C◇(B◇(C◇B))))◇(C◇D))) := congrArg (·◇((D◇(C◇(B◇(C◇B))))◇(C◇D))) ((l4 C B).symm)
   _ = C := (l3 C ((C◇(B◇(C◇B)))) D).symm
 have l19 : ∀ (B C D : G), ((B◇C)◇(B◇(C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B)))) = C := by
  intro B C D
  calc ((B◇C)◇(B◇(C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B))))
   _ = ((B◇C)◇(((((D◇B)◇(((B◇B)◇B)◇D))◇B)◇B)◇(C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B)))) := congrArg ((B◇C)◇·) (congrArg (·◇(C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B))) ((l8 D B).symm))
   _ = C := (l3 C B ((((D◇B)◇(((B◇B)◇B)◇D))◇B))).symm
 have l20 : ∀ (B C : G), ((B◇C)◇((((C◇C)◇C)◇B)◇C)) = C := by
  intro B C
  calc ((B◇C)◇((((C◇C)◇C)◇B)◇C))
   _ = ((B◇C)◇((((C◇C)◇C)◇B)◇(C◇((C◇C)◇C)))) := congrArg ((B◇C)◇·) (congrArg ((((C◇C)◇C)◇B)◇·) ((l17 C).symm))
   _ = C := (l3 C B (((C◇C)◇C))).symm
 have l21 : ∀ (B C : G), ((B◇(B◇B))◇(B◇(B◇(((C◇B)◇(B◇C))◇B)))) = B := by
  intro B C
  calc ((B◇(B◇B))◇(B◇(B◇(((C◇B)◇(B◇C))◇B))))
   _ = ((B◇(B◇B))◇(((((C◇B)◇(B◇C))◇B)◇(B◇(B◇(B◇B))))◇(B◇(((C◇B)◇(B◇C))◇B)))) := congrArg ((B◇(B◇B))◇·) (congrArg (·◇(B◇(((C◇B)◇(B◇C))◇B))) ((l6 C B B B).symm))
   _ = B := l18 B B ((((C◇B)◇(B◇C))◇B))
 have l22x : ∀ (A B : G), (((((A◇A)◇(A◇B))◇A)◇(B◇(A◇A)))◇(((A◇A)◇A)◇(A◇A))) = (B◇(A◇A)) := by
  intro A B
  calc (((((A◇A)◇(A◇B))◇A)◇(B◇(A◇A)))◇(((A◇A)◇A)◇(A◇A)))
   _ = (((((A◇A)◇(A◇B))◇A)◇(B◇(A◇A)))◇((((A◇B)◇((A◇A)◇A))◇(((A◇A)◇(A◇B))◇A))◇(A◇A))) := congrArg (((((A◇A)◇(A◇B))◇A)◇(B◇(A◇A)))◇·) (congrArg (·◇(A◇A)) ((l12 ((A◇B)) A).symm))
   _ = (B◇(A◇A)) := l11 ((((A◇A)◇(A◇B))◇A)) B ((A◇A)) A
 have l22 : ∀ (B C : G), (((((B◇B)◇(B◇C))◇B)◇(C◇(B◇B)))◇B) = (C◇(B◇B)) := by
  intro B C
  have strict_rw_1 := (l22x B C)
  rw [l5] at strict_rw_1
  exact strict_rw_1
 have l23x : ∀ (A : G), ((A◇((((A◇A)◇A)◇(A◇A))◇A))◇(A◇A)) = ((((A◇A)◇A)◇(A◇A))◇A) := by
  intro A
  calc ((A◇((((A◇A)◇A)◇(A◇A))◇A))◇(A◇A))
   _ = ((A◇((((A◇A)◇A)◇(A◇A))◇A))◇(A◇(((((A◇A)◇A)◇(A◇A))◇A)◇((((A◇A)◇A)◇(((A◇A)◇A)◇(A◇A)))◇A)))) := congrArg ((A◇((((A◇A)◇A)◇(A◇A))◇A))◇·) (congrArg (A◇·) ((l20 ((((A◇A)◇A)◇(A◇A))) A).symm))
   _ = ((((A◇A)◇A)◇(A◇A))◇A) := l19 A (((((A◇A)◇A)◇(A◇A))◇A)) ((A◇A))
 have l23 : ∀ (B : G), ((B◇(B◇B))◇(B◇B)) = (B◇B) := by
  intro B
  have strict_rw_2 := (l23x B)
  rw [l5] at strict_rw_2
  exact strict_rw_2
 have l24x : ∀ (A : G), ((A◇(A◇A))◇(A◇(A◇(((((A◇A)◇A)◇A)◇A)◇A)))) = A := by
  intro A
  calc ((A◇(A◇A))◇(A◇(A◇(((((A◇A)◇A)◇A)◇A)◇A))))
   _ = ((A◇(A◇A))◇(A◇(A◇(((((A◇A)◇A)◇A)◇(A◇((A◇A)◇A)))◇A)))) := congrArg ((A◇(A◇A))◇·) (congrArg (A◇·) (congrArg (A◇·) (congrArg (·◇A) (congrArg ((((A◇A)◇A)◇A)◇·) ((l17 A).symm)))))
   _ = A := l21 A (((A◇A)◇A))
 have l24 : ∀ (B : G), ((B◇(B◇B))◇(B◇(B◇B))) = B := by
  intro B
  have strict_rw_3 := (l24x B)
  rw [l9] at strict_rw_3
  exact strict_rw_3
 have l25 : ∀ (B : G), (B◇(B◇(B◇B))) = ((B◇B)◇B) := by
  intro B
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l18 l19 l20 l21 l22x l23x l24x
  grind
 have l26 : ∀ (B C : G), ((((B◇B)◇B)◇C)◇(B◇(C◇B))) = C := by
  intro B C
  calc ((((B◇B)◇B)◇C)◇(B◇(C◇B)))
   _ = ((((B◇B)◇B)◇C)◇((B◇((B◇B)◇B))◇(C◇B))) := congrArg ((((B◇B)◇B)◇C)◇·) (congrArg (·◇(C◇B)) ((l17 B).symm))
   _ = C := (l3 C (((B◇B)◇B)) B).symm
 have l27 : ∀ (B : G), (((B◇B)◇B)◇B) = (B◇(B◇B)) := by
  intro B
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l21 l22x l22 l23x l23 l24x
  grind
 have l28 : ∀ (B : G), ((B◇B)◇((B◇(B◇B))◇B)) = B := by
  intro B
  calc ((B◇B)◇((B◇(B◇B))◇B))
   _ = ((B◇B)◇((((B◇B)◇B)◇B)◇B)) := congrArg ((B◇B)◇·) (congrArg (·◇B) ((l27 B).symm))
   _ = B := l20 B B
 have l29 : ∀ (B C : G), ((B◇((C◇C)◇C))◇((((C◇C)◇C)◇B)◇((C◇C)◇C))) = ((C◇C)◇C) := by
  intro B C
  calc ((B◇((C◇C)◇C))◇((((C◇C)◇C)◇B)◇((C◇C)◇C)))
   _ = ((B◇((C◇C)◇C))◇((((C◇C)◇C)◇B)◇(((C◇C)◇C)◇((C◇C)◇C)))) := congrArg ((B◇((C◇C)◇C))◇·) (congrArg ((((C◇C)◇C)◇B)◇·) ((l13 C).symm))
   _ = ((C◇C)◇C) := (l3 (((C◇C)◇C)) B (((C◇C)◇C))).symm
 have l30 : ∀ (B C D E : G), (B◇((C◇(D◇B))◇(((E◇D)◇(B◇E))◇C))) = ((E◇D)◇(B◇E)) := by
  intro B C D E
  calc (B◇((C◇(D◇B))◇(((E◇D)◇(B◇E))◇C)))
   _ = (((D◇B)◇((E◇D)◇(B◇E)))◇((C◇(D◇B))◇(((E◇D)◇(B◇E))◇C))) := congrArg (·◇((C◇(D◇B))◇(((E◇D)◇(B◇E))◇C))) (((l3 B D E).symm).symm)
   _ = ((E◇D)◇(B◇E)) := (l3 (((E◇D)◇(B◇E))) ((D◇B)) C).symm
 have l31 : ∀ (B : G), ((B◇B)◇(B◇(B◇B))) = (B◇(B◇B)) := by
  intro B
  clear h l4 l5 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l24x l24 l25
  clear l26 l27 l29 l30
  grind
 have l32x : ∀ (A B : G), ((((A◇(B◇B))◇(B◇A))◇((B◇B)◇B))◇(B◇((B◇B)◇B))) = ((B◇B)◇B) := by
  intro A B
  calc ((((A◇(B◇B))◇(B◇A))◇((B◇B)◇B))◇(B◇((B◇B)◇B)))
   _ = ((((A◇(B◇B))◇(B◇A))◇((B◇B)◇B))◇((((B◇B)◇B)◇((A◇(B◇B))◇(B◇A)))◇((B◇B)◇B))) := congrArg ((((A◇(B◇B))◇(B◇A))◇((B◇B)◇B))◇·) (congrArg (·◇((B◇B)◇B)) (((l3 B ((B◇B)) A).symm).symm))
   _ = ((B◇B)◇B) := l29 (((A◇(B◇B))◇(B◇A))) B
 have l32 : ∀ (B C : G), ((((B◇(C◇C))◇(C◇B))◇((C◇C)◇C))◇C) = ((C◇C)◇C) := by
  intro B C
  have strict_rw_4 := (l32x B C)
  rw [l17] at strict_rw_4
  exact strict_rw_4
 have l33 : ∀ (B : G), (B◇((B◇(B◇B))◇B)) = ((B◇B)◇(B◇B)) := by
  intro B
  calc (B◇((B◇(B◇B))◇B))
   _ = (B◇((B◇(B◇B))◇((B◇B)◇((B◇B)◇(B◇B))))) := congrArg (B◇·) (congrArg ((B◇(B◇B))◇·) (l3 B B B))
   _ = (B◇((B◇(B◇B))◇(((B◇B)◇(B◇B))◇((B◇B)◇((B◇B)◇(B◇B)))))) := congrArg (B◇·) (congrArg ((B◇(B◇B))◇·) ((l31 ((B◇B))).symm))
   _ = (B◇((B◇(B◇B))◇(((B◇B)◇(B◇B))◇B))) := congrArg (B◇·) (congrArg ((B◇(B◇B))◇·) (congrArg (((B◇B)◇(B◇B))◇·) ((l3 B B B).symm)))
   _ = ((B◇B)◇(B◇B)) := ((l30 B B B B).symm).symm
 have l34 : ∀ (B C : G), (((B◇B)◇B)◇(((C◇(B◇B))◇(B◇C))◇((B◇B)◇B))) = B := by
  intro B C
  clear h l3 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l18 l19 l20 l21 l22x l22 l23x l23 l24x l24
  clear l25 l26 l27 l28 l29 l30 l31 l32x l33
  grind
 have l35 : ∀ (B C : G), ((((B◇C)◇(C◇B))◇C)◇((C◇C)◇C)) = C := by
  intro B C
  calc ((((B◇C)◇(C◇B))◇C)◇((C◇C)◇C))
   _ = ((((B◇C)◇(C◇B))◇C)◇(C◇(C◇(C◇C)))) := congrArg ((((B◇C)◇(C◇B))◇C)◇·) ((l25 C).symm)
   _ = C := l6 B C C C
 have l36 : ∀ (B : G), ((B◇(B◇B))◇B) = ((B◇B)◇(B◇B)) := by
  intro B
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l25 l26 l27 l28 l29 l30 l32x l32 l34 l35
  grind
 have l37 : ∀ (B C : G), ((B◇(C◇C))◇(C◇B)) = (C◇C) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x l24
  clear l25 l27 l28 l29 l30 l31 l32x l32 l33 l35 l36
  grind
 have l38 : ∀ (B : G), (B◇((B◇B)◇(B◇B))) = ((B◇B)◇(B◇B)) := by
  intro B
  calc (B◇((B◇B)◇(B◇B)))
   _ = (((B◇B)◇((B◇B)◇(B◇B)))◇((B◇B)◇(B◇B))) := congrArg (·◇((B◇B)◇(B◇B))) (((l3 B B B).symm).symm)
   _ = ((B◇B)◇(B◇B)) := l23 ((B◇B))
 have l39 : ∀ (B C D : G), ((((B◇B)◇B)◇C)◇(B◇(C◇(((D◇B)◇(B◇D))◇B)))) = C := by
  intro B C D
  calc ((((B◇B)◇B)◇C)◇(B◇(C◇(((D◇B)◇(B◇D))◇B))))
   _ = ((((B◇B)◇B)◇C)◇(((((D◇B)◇(B◇D))◇B)◇((B◇B)◇B))◇(C◇(((D◇B)◇(B◇D))◇B)))) := congrArg ((((B◇B)◇B)◇C)◇·) (congrArg (·◇(C◇(((D◇B)◇(B◇D))◇B))) ((l35 D B).symm))
   _ = C := (l3 C (((B◇B)◇B)) ((((D◇B)◇(B◇D))◇B))).symm
 have l40 : ∀ (B : G), (((B◇B)◇B)◇(B◇(B◇B))) = ((B◇B)◇(B◇B)) := by
  intro B
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l26 l28 l29 l30 l31 l32x l32 l33 l34 l35 l37 l38 l39
  grind
 have l41 : ∀ (B C : G), ((B◇C)◇((C◇(C◇C))◇B)) = C := by
  intro B C
  calc ((B◇C)◇((C◇(C◇C))◇B))
   _ = ((B◇((C◇(C◇C))◇(C◇(C◇C))))◇((C◇(C◇C))◇B)) := congrArg (·◇((C◇(C◇C))◇B)) (congrArg (B◇·) ((l24 C).symm))
   _ = ((C◇(C◇C))◇(C◇(C◇C))) := l37 B ((C◇(C◇C)))
   _ = C := ((l24 C).symm).symm
 have l42 : ∀ (B C : G), ((B◇(C◇C))◇(((C◇(C◇C))◇B)◇(C◇(C◇C)))) = (C◇C) := by
  intro B C
  calc ((B◇(C◇C))◇(((C◇(C◇C))◇B)◇(C◇(C◇C))))
   _ = ((B◇(C◇C))◇(((C◇(C◇C))◇B)◇((C◇C)◇(C◇(C◇C))))) := congrArg ((B◇(C◇C))◇·) (congrArg (((C◇(C◇C))◇B)◇·) ((l31 C).symm))
   _ = (C◇C) := (l3 ((C◇C)) B ((C◇(C◇C)))).symm
 have l43 : ∀ (B C : G), ((((B◇C)◇(C◇B))◇(C◇C))◇((C◇C)◇(C◇C))) = (C◇C) := by
  intro B C
  calc ((((B◇C)◇(C◇B))◇(C◇C))◇((C◇C)◇(C◇C)))
   _ = ((((B◇C)◇(C◇B))◇(C◇C))◇(C◇((C◇C)◇(C◇C)))) := congrArg ((((B◇C)◇(C◇B))◇(C◇C))◇·) ((l38 C).symm)
   _ = (C◇C) := l6 B C C ((C◇C))
 have l44 : ∀ (B C : G), ((B◇C)◇(((B◇B)◇(B◇B))◇(C◇(B◇(B◇B))))) = C := by
  intro B C
  calc ((B◇C)◇(((B◇B)◇(B◇B))◇(C◇(B◇(B◇B)))))
   _ = ((B◇C)◇(((B◇(B◇B))◇B)◇(C◇(B◇(B◇B))))) := congrArg ((B◇C)◇·) (congrArg (·◇(C◇(B◇(B◇B)))) ((l36 B).symm))
   _ = C := (l3 C B ((B◇(B◇B)))).symm
 have l45 : ∀ (B C : G), (((B◇B)◇(B◇B))◇((C◇B)◇(B◇C))) = (B◇(B◇B)) := by
  intro B C
  calc (((B◇B)◇(B◇B))◇((C◇B)◇(B◇C)))
   _ = ((((B◇B)◇B)◇(B◇(B◇B)))◇((C◇B)◇(B◇C))) := congrArg (·◇((C◇B)◇(B◇C))) ((l40 B).symm)
   _ = ((((B◇B)◇B)◇(B◇(B◇B)))◇(B◇((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B)))) := congrArg ((((B◇B)◇B)◇(B◇(B◇B)))◇·) ((l30 B B B C).symm)
   _ = (B◇(B◇B)) := ((l39 B ((B◇(B◇B))) C).symm).symm
 have l46 : ∀ (B C D : G), ((B◇(C◇D))◇((((D◇(D◇D))◇C)◇B)◇D)) = (C◇D) := by
  intro B C D
  calc ((B◇(C◇D))◇((((D◇(D◇D))◇C)◇B)◇D))
   _ = ((B◇(C◇D))◇((((D◇(D◇D))◇C)◇B)◇((C◇D)◇((D◇(D◇D))◇C)))) := congrArg ((B◇(C◇D))◇·) (congrArg ((((D◇(D◇D))◇C)◇B)◇·) ((l41 C D).symm))
   _ = (C◇D) := (l3 ((C◇D)) B (((D◇(D◇D))◇C))).symm
 have l47 : ∀ (B C : G), ((B◇B)◇((B◇(((C◇B)◇(B◇C))◇(B◇B)))◇B)) = ((B◇B)◇(B◇B)) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l44 l45 l46
  grind
 have l48 : ∀ (B C : G), ((B◇(B◇B))◇(B◇(((C◇B)◇(B◇C))◇(B◇B)))) = ((C◇B)◇(B◇C)) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l46 l47
  grind
 have l49 : ∀ (B C D : G), ((B◇C)◇((D◇(B◇D))◇(C◇(B◇(D◇(B◇D)))))) = C := by
  intro B C D
  calc ((B◇C)◇((D◇(B◇D))◇(C◇(B◇(D◇(B◇D))))))
   _ = ((B◇C)◇(((B◇(D◇(B◇D)))◇B)◇(C◇(B◇(D◇(B◇D)))))) := congrArg ((B◇C)◇·) (congrArg (·◇(C◇(B◇(D◇(B◇D))))) ((l4 B D).symm))
   _ = C := (l3 C B ((B◇(D◇(B◇D))))).symm
 have l50 : ∀ (B : G), (((B◇B)◇(B◇B))◇(B◇B)) = ((B◇B)◇B) := by
  intro B
  calc (((B◇B)◇(B◇B))◇(B◇B))
   _ = ((B◇B)◇((B◇B)◇((B◇B)◇(B◇B)))) := (l25 ((B◇B))).symm
   _ = ((B◇B)◇B) := congrArg ((B◇B)◇·) ((l3 B B B).symm)
 have l51 : ∀ (B : G), ((B◇B)◇((B◇B)◇B)) = (B◇B) := by
  intro B
  clear h l4 l5 l6 l7 l8 l9 l10 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l24x l24 l25
  clear l26 l27 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47 l48 l49
  clear l50
  grind
 have l52 : ∀ (B C : G), ((B◇C)◇(((C◇(C◇C))◇B)◇((C◇C)◇C))) = C := by
  intro B C
  calc ((B◇C)◇(((C◇(C◇C))◇B)◇((C◇C)◇C)))
   _ = ((B◇C)◇(((C◇(C◇C))◇B)◇(C◇(C◇(C◇C))))) := congrArg ((B◇C)◇·) (congrArg (((C◇(C◇C))◇B)◇·) ((l25 C).symm))
   _ = C := (l3 C B ((C◇(C◇C)))).symm
 have l53x : ∀ (A B : G), (((A◇A)◇(A◇A))◇((((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇(A◇A))◇A)) = ((A◇(((B◇A)◇(A◇B))◇(A◇A)))◇A) := by
  intro A B
  calc (((A◇A)◇(A◇A))◇((((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇(A◇A))◇A))
   _ = (((A◇A)◇((A◇(((B◇A)◇(A◇B))◇(A◇A)))◇A))◇((((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇(A◇A))◇A)) := congrArg (·◇((((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇(A◇A))◇A)) ((l47 A B).symm)
   _ = ((A◇(((B◇A)◇(A◇B))◇(A◇A)))◇A) := l46 ((A◇A)) ((A◇(((B◇A)◇(A◇B))◇(A◇A)))) A
 have l53 : ∀ (B C : G), ((B◇(((C◇B)◇(B◇C))◇(B◇B)))◇B) = (B◇B) := by
  intro B C
  have strict_rw_5 := ((l53x B C).symm)
  rw [l48, l11] at strict_rw_5
  exact strict_rw_5
 have l54 : ∀ (B C : G), ((((B◇B)◇(B◇B))◇C)◇((B◇B)◇(C◇((B◇B)◇B)))) = C := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l52 l53x l53
  grind
 have l55x : ∀ (A B : G), ((A◇A)◇(((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇((A◇A)◇A))) = A := by
  intro A B
  calc ((A◇A)◇(((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇((A◇A)◇A)))
   _ = (((A◇(((B◇A)◇(A◇B))◇(A◇A)))◇A)◇(((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇((A◇A)◇A))) := congrArg (·◇(((A◇(A◇A))◇(A◇(((B◇A)◇(A◇B))◇(A◇A))))◇((A◇A)◇A))) ((l53 A B).symm)
   _ = A := l52 ((A◇(((B◇A)◇(A◇B))◇(A◇A)))) A
 have l55 : ∀ (B C : G), ((B◇B)◇(((C◇B)◇(B◇C))◇((B◇B)◇B))) = B := by
  intro B C
  have strict_rw_6 := (l55x B C)
  rw [l48] at strict_rw_6
  exact strict_rw_6
 have l56 : ∀ (B C : G), ((B◇B)◇(B◇B)) = ((C◇B)◇(B◇C)) := by
  intro B C
  calc ((B◇B)◇(B◇B))
   _ = ((B◇(B◇B))◇B) := (l36 B).symm
   _ = ((B◇(B◇B))◇((B◇B)◇(((C◇B)◇(B◇C))◇((B◇B)◇B)))) := congrArg ((B◇(B◇B))◇·) ((l55 B C).symm)
   _ = ((((B◇B)◇(B◇B))◇((C◇B)◇(B◇C)))◇((B◇B)◇(((C◇B)◇(B◇C))◇((B◇B)◇B)))) := congrArg (·◇((B◇B)◇(((C◇B)◇(B◇C))◇((B◇B)◇B)))) ((l45 B C).symm)
   _ = ((C◇B)◇(B◇C)) := ((l54 B (((C◇B)◇(B◇C)))).symm).symm
 have l57 : ∀ (B C : G), (B◇((C◇((B◇B)◇B))◇((B◇B)◇C))) = (B◇B) := by
  intro B C
  calc (B◇((C◇((B◇B)◇B))◇((B◇B)◇C)))
   _ = ((((B◇B)◇B)◇(B◇B))◇((C◇((B◇B)◇B))◇((B◇B)◇C))) := congrArg (·◇((C◇((B◇B)◇B))◇((B◇B)◇C))) ((l5 B).symm)
   _ = (B◇B) := (l3 ((B◇B)) (((B◇B)◇B)) C).symm
 have l58 : ∀ (B C D : G), (((B◇(C◇(B◇(B◇B))))◇D)◇(C◇(D◇((B◇(B◇B))◇C)))) = D := by
  intro B C D
  calc (((B◇(C◇(B◇(B◇B))))◇D)◇(C◇(D◇((B◇(B◇B))◇C))))
   _ = (((((B◇(B◇B))◇(B◇(B◇B)))◇(C◇(B◇(B◇B))))◇D)◇(C◇(D◇((B◇(B◇B))◇C)))) := congrArg (·◇(C◇(D◇((B◇(B◇B))◇C)))) (congrArg (·◇D) (congrArg (·◇(C◇(B◇(B◇B)))) ((l24 B).symm)))
   _ = D := l6 ((B◇(B◇B))) ((B◇(B◇B))) C D
 have l59 : ∀ (B C : G), (((B◇C)◇(C◇B))◇C) = C := by
  intro B C
  calc (((B◇C)◇(C◇B))◇C)
   _ = (((C◇C)◇(C◇C))◇C) := congrArg (·◇C) ((l56 C B).symm)
   _ = (((C◇C)◇(C◇C))◇((C◇C)◇((C◇C)◇(C◇C)))) := congrArg (((C◇C)◇(C◇C))◇·) (l3 C C C)
   _ = ((C◇C)◇((C◇C)◇(C◇C))) := ((l31 ((C◇C))).symm).symm
   _ = C := (l3 C C C).symm
 have l60x : ∀ (A B : G), ((((A◇(((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B))))◇(((B◇(B◇B))◇(B◇(B◇B)))◇A))◇B)◇(((B◇(B◇B))◇(B◇(B◇B)))◇((B◇B)◇B))) = B := by
  intro A B
  calc ((((A◇(((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B))))◇(((B◇(B◇B))◇(B◇(B◇B)))◇A))◇B)◇(((B◇(B◇B))◇(B◇(B◇B)))◇((B◇B)◇B)))
   _ = ((((A◇(((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B))))◇(((B◇(B◇B))◇(B◇(B◇B)))◇A))◇B)◇(((B◇(B◇B))◇((A◇(((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B))))◇(((B◇(B◇B))◇(B◇(B◇B)))◇A)))◇((B◇B)◇B))) := congrArg ((((A◇(((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B))))◇(((B◇(B◇B))◇(B◇(B◇B)))◇A))◇B)◇·) (congrArg (·◇((B◇B)◇B)) ((l57 ((B◇(B◇B))) A).symm))
   _ = B := l52 (((A◇(((B◇(B◇B))◇(B◇(B◇B)))◇(B◇(B◇B))))◇(((B◇(B◇B))◇(B◇(B◇B)))◇A))) B
 have l60 : ∀ (B C : G), ((((B◇((C◇C)◇C))◇(C◇B))◇C)◇C) = C := by
  intro B C
  have strict_rw_7 := (l60x B C)
  rw [l24, l25, l17] at strict_rw_7
  exact strict_rw_7
 have l61x : ∀ (A B : G), (((A◇(B◇(A◇(A◇A))))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇(B◇((A◇(A◇A))◇(A◇(A◇A))))) = (B◇((A◇(A◇A))◇(A◇(A◇A)))) := by
  intro A B
  calc (((A◇(B◇(A◇(A◇A))))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))
   _ = (((A◇(B◇(A◇(A◇A))))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇(B◇((B◇((A◇(A◇A))◇(A◇(A◇A))))◇((A◇(A◇A))◇B)))) := congrArg (((A◇(B◇(A◇(A◇A))))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇·) (congrArg (B◇·) ((l37 B ((A◇(A◇A)))).symm))
   _ = (B◇((A◇(A◇A))◇(A◇(A◇A)))) := l58 A B ((B◇((A◇(A◇A))◇(A◇(A◇A)))))
 have l61 : ∀ (B C : G), (((B◇(C◇(B◇(B◇B))))◇(C◇B))◇(C◇B)) = (C◇B) := by
  intro B C
  have strict_rw_8 := (l61x B C)
  rw [l24] at strict_rw_8
  exact strict_rw_8
 have l62 : ∀ (B C D : G), ((((B◇C)◇((D◇C)◇B))◇((D◇C)◇D))◇C) = ((D◇C)◇D) := by
  intro B C D
  calc ((((B◇C)◇((D◇C)◇B))◇((D◇C)◇D))◇C)
   _ = ((((B◇C)◇((D◇C)◇B))◇((D◇C)◇D))◇((D◇C)◇(((D◇C)◇D)◇(C◇(D◇C))))) := congrArg ((((B◇C)◇((D◇C)◇B))◇((D◇C)◇D))◇·) (((l3 C D ((D◇C))).symm).symm)
   _ = ((D◇C)◇D) := l6 B C ((D◇C)) (((D◇C)◇D))
 have l63 : ∀ (B C : G), ((B◇(B◇(((C◇B)◇(((B◇B)◇B)◇C))◇B)))◇B) = B := by
  intro B C
  calc ((B◇(B◇(((C◇B)◇(((B◇B)◇B)◇C))◇B)))◇B)
   _ = ((((((C◇B)◇(((B◇B)◇B)◇C))◇B)◇B)◇(B◇(((C◇B)◇(((B◇B)◇B)◇C))◇B)))◇B) := congrArg (·◇B) (congrArg (·◇(B◇(((C◇B)◇(((B◇B)◇B)◇C))◇B))) ((l8 C B).symm))
   _ = B := l59 ((((C◇B)◇(((B◇B)◇B)◇C))◇B)) B
 have l64 : ∀ (B C : G), ((B◇(B◇(((C◇((B◇B)◇B))◇(B◇C))◇B)))◇B) = B := by
  intro B C
  calc ((B◇(B◇(((C◇((B◇B)◇B))◇(B◇C))◇B)))◇B)
   _ = ((((((C◇((B◇B)◇B))◇(B◇C))◇B)◇B)◇(B◇(((C◇((B◇B)◇B))◇(B◇C))◇B)))◇B) := congrArg (·◇B) (congrArg (·◇(B◇(((C◇((B◇B)◇B))◇(B◇C))◇B))) ((l60 C B).symm))
   _ = B := l59 ((((C◇((B◇B)◇B))◇(B◇C))◇B)) B
 have l65 : ∀ (B C : G), ((B◇C)◇(B◇(C◇((((B◇B)◇B)◇B)◇B)))) = C := by
  intro B C
  calc ((B◇C)◇(B◇(C◇((((B◇B)◇B)◇B)◇B))))
   _ = ((B◇C)◇((((((B◇B)◇B)◇B)◇B)◇B)◇(C◇((((B◇B)◇B)◇B)◇B)))) := congrArg ((B◇C)◇·) (congrArg (·◇(C◇((((B◇B)◇B)◇B)◇B))) ((l9 B).symm))
   _ = C := (l3 C B (((((B◇B)◇B)◇B)◇B))).symm
 have l66 : ∀ (B C : G), (B◇((C◇B)◇(B◇C))) = ((C◇B)◇(B◇C)) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l52 l53x l53 l54 l55x l55 l57 l58 l59 l60x l60 l61x l62 l63 l64 l65
  grind
 have l67 : ∀ (B C : G), ((B◇B)◇(B◇(((C◇B)◇(((B◇B)◇B)◇C))◇B))) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l64 l65 l66
  grind
 have l68 : ∀ (B C D : G), (B◇((C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B))◇(B◇C))) = B := by
  intro B C D
  calc (B◇((C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B))◇(B◇C)))
   _ = (((((D◇B)◇(((B◇B)◇B)◇D))◇B)◇B)◇((C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B))◇(B◇C))) := congrArg (·◇((C◇(((D◇B)◇(((B◇B)◇B)◇D))◇B))◇(B◇C))) ((l8 D B).symm)
   _ = B := (l3 B ((((D◇B)◇(((B◇B)◇B)◇D))◇B)) C).symm
 have l69 : ∀ (B C : G), ((B◇B)◇(B◇(((C◇((B◇B)◇B))◇(B◇C))◇B))) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l63 l65 l66 l67
  clear l68
  grind
 have l70 : ∀ (B C D : G), (B◇((C◇(((D◇((B◇B)◇B))◇(B◇D))◇B))◇(B◇C))) = B := by
  intro B C D
  calc (B◇((C◇(((D◇((B◇B)◇B))◇(B◇D))◇B))◇(B◇C)))
   _ = (((((D◇((B◇B)◇B))◇(B◇D))◇B)◇B)◇((C◇(((D◇((B◇B)◇B))◇(B◇D))◇B))◇(B◇C))) := congrArg (·◇((C◇(((D◇((B◇B)◇B))◇(B◇D))◇B))◇(B◇C))) ((l60 D B).symm)
   _ = B := (l3 B ((((D◇((B◇B)◇B))◇(B◇D))◇B)) C).symm
 have l71 : ∀ (B : G), ((B◇(B◇B))◇((B◇B)◇B)) = (B◇(B◇B)) := by
  intro B
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l25 l26 l28 l29 l30 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47 l48 l49
  clear l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l66 l67 l68 l69 l70
  grind
 have l72 : ∀ (B C D : G), ((B◇C)◇(B◇(C◇(((D◇((B◇B)◇B))◇(B◇D))◇B)))) = C := by
  intro B C D
  calc ((B◇C)◇(B◇(C◇(((D◇((B◇B)◇B))◇(B◇D))◇B))))
   _ = ((B◇C)◇(((((D◇((B◇B)◇B))◇(B◇D))◇B)◇B)◇(C◇(((D◇((B◇B)◇B))◇(B◇D))◇B)))) := congrArg ((B◇C)◇·) (congrArg (·◇(C◇(((D◇((B◇B)◇B))◇(B◇D))◇B))) ((l60 D B).symm))
   _ = C := (l3 C B ((((D◇((B◇B)◇B))◇(B◇D))◇B))).symm
 have l73 : ∀ (B C D E : G), ((((B◇(C◇D))◇((E◇C)◇B))◇(D◇E))◇((E◇C)◇E)) = (D◇E) := by
  intro B C D E
  calc ((((B◇(C◇D))◇((E◇C)◇B))◇(D◇E))◇((E◇C)◇E))
   _ = ((((B◇(C◇D))◇((E◇C)◇B))◇(D◇E))◇((E◇C)◇((D◇E)◇((C◇D)◇(E◇C))))) := congrArg ((((B◇(C◇D))◇((E◇C)◇B))◇(D◇E))◇·) (congrArg ((E◇C)◇·) (((l3 E D C).symm).symm))
   _ = (D◇E) := l6 B ((C◇D)) ((E◇C)) ((D◇E))
 have l74 : ∀ (B C : G), ((B◇(((C◇B)◇(((B◇B)◇B)◇C))◇B))◇B) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65
  clear l69 l70 l71 l72 l73
  grind
 have l75 : ∀ (B C D : G), ((B◇C)◇(C◇B)) = ((D◇C)◇(C◇D)) := by
  intro B C D
  calc ((B◇C)◇(C◇B))
   _ = ((C◇C)◇(C◇C)) := (l56 C B).symm
   _ = ((D◇C)◇(C◇D)) := l56 C D
 have l76 : ∀ (B C : G), ((B◇(((C◇((B◇B)◇B))◇(B◇C))◇B))◇B) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65
  clear l67 l68 l71 l72 l73 l74 l75
  grind
 have l77 : ∀ (B C : G), (B◇(((C◇B)◇(B◇C))◇(B◇B))) = B := by
  intro B C
  calc (B◇(((C◇B)◇(B◇C))◇(B◇B)))
   _ = (((B◇B)◇((B◇B)◇(B◇B)))◇(((C◇B)◇(B◇C))◇(B◇B))) := congrArg (·◇(((C◇B)◇(B◇C))◇(B◇B))) (l3 B B B)
   _ = (((B◇B)◇((B◇B)◇(B◇B)))◇(((B◇B)◇(B◇B))◇(B◇B))) := congrArg (((B◇B)◇((B◇B)◇(B◇B)))◇·) (congrArg (·◇(B◇B)) ((l56 B C).symm))
   _ = ((B◇B)◇((B◇B)◇(B◇B))) := ((l71 ((B◇B))).symm).symm
   _ = B := (l3 B B B).symm
 have l78x : ∀ (A B : G), ((A◇(A◇(((A◇A)◇A)◇A)))◇((B◇((A◇A)◇A))◇(A◇B))) = (A◇(((A◇A)◇A)◇A)) := by
  intro A B
  calc ((A◇(A◇(((A◇A)◇A)◇A)))◇((B◇((A◇A)◇A))◇(A◇B)))
   _ = ((A◇(A◇(((A◇A)◇A)◇A)))◇(A◇((A◇(((A◇A)◇A)◇A))◇(((B◇((A◇A)◇A))◇(A◇B))◇A)))) := congrArg ((A◇(A◇(((A◇A)◇A)◇A)))◇·) ((l30 A A (((A◇A)◇A)) B).symm)
   _ = (A◇(((A◇A)◇A)◇A)) := l72 A ((A◇(((A◇A)◇A)◇A))) B
 have l78 : ∀ (B C : G), (B◇((C◇((B◇B)◇B))◇(B◇C))) = ((B◇B)◇B) := by
  intro B C
  have strict_rw_9 := (l78x B C)
  rw [l27, l25, l17] at strict_rw_9
  exact strict_rw_9
 have l79 : ∀ (B C : G), ((((B◇(B◇C))◇(B◇(B◇B)))◇(C◇(B◇B)))◇B) = (C◇(B◇B)) := by
  intro B C
  calc ((((B◇(B◇C))◇(B◇(B◇B)))◇(C◇(B◇B)))◇B)
   _ = ((((B◇(B◇C))◇(((B◇B)◇B)◇B))◇(C◇(B◇B)))◇B) := congrArg (·◇B) (congrArg (·◇(C◇(B◇B))) (congrArg ((B◇(B◇C))◇·) ((l27 B).symm)))
   _ = ((((B◇(B◇C))◇(((B◇B)◇B)◇B))◇(C◇(B◇B)))◇(((B◇B)◇B)◇(B◇B))) := congrArg ((((B◇(B◇C))◇(((B◇B)◇B)◇B))◇(C◇(B◇B)))◇·) ((l5 B).symm)
   _ = (C◇(B◇B)) := ((l73 B B C ((B◇B))).symm).symm
 have l80 : ∀ (B C D : G), (((B◇C)◇(((D◇B)◇(C◇D))◇C))◇(B◇C)) = (((D◇B)◇(C◇D))◇C) := by
  intro B C D
  clear h l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x l24
  clear l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47
  clear l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66 l67
  clear l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79
  grind
 have l81 : ∀ (B C : G), (B◇(B◇((B◇B)◇(((C◇B)◇(B◇C))◇B)))) = (B◇B) := by
  intro B C
  calc (B◇(B◇((B◇B)◇(((C◇B)◇(B◇C))◇B))))
   _ = (B◇(((((C◇B)◇(B◇C))◇B)◇((B◇B)◇B))◇((B◇B)◇(((C◇B)◇(B◇C))◇B)))) := congrArg (B◇·) (congrArg (·◇((B◇B)◇(((C◇B)◇(B◇C))◇B))) ((l35 C B).symm))
   _ = (B◇B) := l57 B ((((C◇B)◇(B◇C))◇B))
 have l82 : ∀ (B C : G), (((B◇(B◇B))◇C)◇((B◇(B◇B))◇(C◇(B◇B)))) = C := by
  intro B C
  calc (((B◇(B◇B))◇C)◇((B◇(B◇B))◇(C◇(B◇B))))
   _ = (((B◇(B◇B))◇C)◇(((B◇B)◇(B◇(B◇B)))◇(C◇(B◇B)))) := congrArg (((B◇(B◇B))◇C)◇·) (congrArg (·◇(C◇(B◇B))) ((l31 B).symm))
   _ = C := (l3 C ((B◇(B◇B))) ((B◇B))).symm
 have l83 : ∀ (B C : G), ((B◇(B◇B))◇((C◇(B◇B))◇((B◇B)◇C))) = B := by
  intro B C
  calc ((B◇(B◇B))◇((C◇(B◇B))◇((B◇B)◇C)))
   _ = ((((B◇B)◇(B◇B))◇((B◇B)◇(B◇B)))◇((C◇(B◇B))◇((B◇B)◇C))) := congrArg (·◇((C◇(B◇B))◇((B◇B)◇C))) ((l45 B B).symm)
   _ = ((B◇B)◇((B◇B)◇(B◇B))) := l45 ((B◇B)) C
   _ = B := (l3 B B B).symm
 have l84x : ∀ (A B : G), ((((A◇B)◇((B◇B)◇A))◇B)◇((B◇B)◇((B◇B)◇B))) = B := by
  intro A B
  calc ((((A◇B)◇((B◇B)◇A))◇B)◇((B◇B)◇((B◇B)◇B)))
   _ = ((((A◇B)◇((B◇B)◇A))◇B)◇(((B◇(B◇B))◇((A◇B)◇((B◇B)◇A)))◇((B◇B)◇B))) := congrArg ((((A◇B)◇((B◇B)◇A))◇B)◇·) (congrArg (·◇((B◇B)◇B)) (((l3 ((B◇B)) B A).symm).symm))
   _ = B := l52 (((A◇B)◇((B◇B)◇A))) B
 have l84 : ∀ (B C : G), ((((B◇C)◇((C◇C)◇B))◇C)◇(C◇C)) = C := by
  intro B C
  have strict_rw_10 := (l84x B C)
  rw [l51] at strict_rw_10
  exact strict_rw_10
 have l85 : ∀ (B C : G), ((B◇B)◇(((C◇B)◇(((B◇B)◇B)◇C))◇B)) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84
  grind
 have l86 : ∀ (B C : G), (B◇((C◇B)◇(((B◇B)◇B)◇C))) = ((B◇B)◇B) := by
  intro B C
  calc (B◇((C◇B)◇(((B◇B)◇B)◇C)))
   _ = ((B◇((B◇B)◇B))◇((C◇B)◇(((B◇B)◇B)◇C))) := congrArg (·◇((C◇B)◇(((B◇B)◇B)◇C))) ((l17 B).symm)
   _ = ((B◇B)◇B) := (l3 (((B◇B)◇B)) B C).symm
 have l87 : ∀ (B C D E : G), (((B◇C)◇D)◇(((E◇B)◇(B◇E))◇(D◇(C◇B)))) = D := by
  intro B C D E
  calc (((B◇C)◇D)◇(((E◇B)◇(B◇E))◇(D◇(C◇B))))
   _ = (((B◇C)◇D)◇(((C◇B)◇(B◇C))◇(D◇(C◇B)))) := congrArg (((B◇C)◇D)◇·) (congrArg (·◇(D◇(C◇B))) ((l75 C B E).symm))
   _ = D := (l3 D ((B◇C)) ((C◇B))).symm
 have l88 : ∀ (B C : G), ((B◇B)◇(((C◇((B◇B)◇B))◇(B◇C))◇B)) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87
  grind
 have l89x : ∀ (A B : G), (A◇(A◇((((B◇A)◇(A◇B))◇(A◇A))◇((((A◇A)◇A)◇A)◇A)))) = (((B◇A)◇(A◇B))◇(A◇A)) := by
  intro A B
  calc (A◇(A◇((((B◇A)◇(A◇B))◇(A◇A))◇((((A◇A)◇A)◇A)◇A))))
   _ = ((A◇(((B◇A)◇(A◇B))◇(A◇A)))◇(A◇((((B◇A)◇(A◇B))◇(A◇A))◇((((A◇A)◇A)◇A)◇A)))) := congrArg (·◇(A◇((((B◇A)◇(A◇B))◇(A◇A))◇((((A◇A)◇A)◇A)◇A)))) ((l77 A B).symm)
   _ = (((B◇A)◇(A◇B))◇(A◇A)) := l65 A ((((B◇A)◇(A◇B))◇(A◇A)))
 have l89 : ∀ (B C : G), (((B◇C)◇(C◇B))◇(C◇C)) = ((C◇C)◇C) := by
  intro B C
  have strict_rw_11 := ((l89x C B).symm)
  rw [l27, l36, l43, l25] at strict_rw_11
  exact strict_rw_11
 have l90 : ∀ (B C : G), ((B◇B)◇((C◇((B◇B)◇B))◇((B◇B)◇C))) = ((B◇B)◇B) := by
  intro B C
  calc ((B◇B)◇((C◇((B◇B)◇B))◇((B◇B)◇C)))
   _ = ((B◇B)◇((C◇(((B◇B)◇(B◇B))◇(B◇B)))◇((B◇B)◇C))) := congrArg ((B◇B)◇·) (congrArg (·◇((B◇B)◇C)) (congrArg (C◇·) ((l50 B).symm)))
   _ = (((B◇B)◇(B◇B))◇(B◇B)) := l78 ((B◇B)) C
   _ = ((B◇B)◇B) := ((l50 B).symm).symm
 have l91 : ∀ (B C : G), (((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B))◇B) = (((C◇B)◇(B◇C))◇B) := by
  intro B C
  calc (((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B))◇B)
   _ = ((((B◇B)◇(B◇(B◇B)))◇(((C◇B)◇(B◇C))◇B))◇B) := congrArg (·◇B) (congrArg (·◇(((C◇B)◇(B◇C))◇B)) ((l31 B).symm))
   _ = ((((B◇(B◇((B◇B)◇(((C◇B)◇(B◇C))◇B))))◇(B◇(B◇B)))◇(((C◇B)◇(B◇C))◇B))◇B) := congrArg (·◇B) (congrArg (·◇(((C◇B)◇(B◇C))◇B)) (congrArg (·◇(B◇(B◇B))) ((l81 B C).symm)))
   _ = ((((B◇(B◇((B◇B)◇(((C◇B)◇(B◇C))◇B))))◇(B◇(B◇B)))◇(((B◇B)◇(((C◇B)◇(B◇C))◇B))◇(B◇B)))◇B) := congrArg (·◇B) (congrArg (((B◇(B◇((B◇B)◇(((C◇B)◇(B◇C))◇B))))◇(B◇(B◇B)))◇·) ((l80 B B C).symm))
   _ = (((B◇B)◇(((C◇B)◇(B◇C))◇B))◇(B◇B)) := ((l79 B (((B◇B)◇(((C◇B)◇(B◇C))◇B)))).symm).symm
   _ = (((C◇B)◇(B◇C))◇B) := ((l80 B B C).symm).symm
 have l92x : ∀ (A B : G), (((A◇(A◇A))◇((B◇(A◇A))◇((A◇A)◇B)))◇((A◇(A◇A))◇(A◇A))) = ((B◇(A◇A))◇((A◇A)◇B)) := by
  intro A B
  calc (((A◇(A◇A))◇((B◇(A◇A))◇((A◇A)◇B)))◇((A◇(A◇A))◇(A◇A)))
   _ = (((A◇(A◇A))◇((B◇(A◇A))◇((A◇A)◇B)))◇((A◇(A◇A))◇(((B◇(A◇A))◇((A◇A)◇B))◇(A◇A)))) := congrArg (((A◇(A◇A))◇((B◇(A◇A))◇((A◇A)◇B)))◇·) (congrArg ((A◇(A◇A))◇·) ((l59 B ((A◇A))).symm))
   _ = ((B◇(A◇A))◇((A◇A)◇B)) := l82 A (((B◇(A◇A))◇((A◇A)◇B)))
 have l92 : ∀ (B C : G), ((B◇(C◇C))◇((C◇C)◇B)) = (C◇(C◇C)) := by
  intro B C
  have strict_rw_12 := ((l92x C B).symm)
  rw [l83, l37] at strict_rw_12
  exact strict_rw_12
 have l93 : ∀ (B C : G), ((((B◇(C◇(C◇C)))◇(C◇B))◇(C◇(C◇C)))◇C) = (C◇(C◇C)) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l85 l86 l87 l88 l89x
  clear l89 l90 l91 l92x l92
  grind
 have l94 : ∀ (B C D : G), (((B◇(C◇B))◇D)◇(C◇(D◇(((B◇B)◇B)◇C)))) = D := by
  intro B C D
  calc (((B◇(C◇B))◇D)◇(C◇(D◇(((B◇B)◇B)◇C))))
   _ = ((((B◇((B◇B)◇B))◇(C◇B))◇D)◇(C◇(D◇(((B◇B)◇B)◇C)))) := congrArg (·◇(C◇(D◇(((B◇B)◇B)◇C)))) (congrArg (·◇D) (congrArg (·◇(C◇B)) ((l17 B).symm)))
   _ = D := l6 B (((B◇B)◇B)) C D
 have l95x : ∀ (A B : G), ((A◇B)◇(((B◇B)◇B)◇A)) = ((B◇((A◇B)◇(((B◇B)◇B)◇A)))◇B) := by
  intro A B
  calc ((A◇B)◇(((B◇B)◇B)◇A))
   _ = ((B◇((A◇B)◇(((B◇B)◇B)◇A)))◇((B◇B)◇(((A◇B)◇(((B◇B)◇B)◇A))◇B))) := l3 (((A◇B)◇(((B◇B)◇B)◇A))) B B
   _ = ((B◇((A◇B)◇(((B◇B)◇B)◇A)))◇B) := congrArg ((B◇((A◇B)◇(((B◇B)◇B)◇A)))◇·) (l85 B A)
 have l95 : ∀ (B C : G), ((B◇C)◇(((C◇C)◇C)◇B)) = (C◇(C◇C)) := by
  intro B C
  have strict_rw_13 := (l95x B C)
  rw [l86, l27] at strict_rw_13
  exact strict_rw_13
 have l96x : ∀ (A B : G), (((A◇A)◇((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B)))◇(A◇A)) = ((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B)) := by
  intro A B
  calc (((A◇A)◇((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B)))◇(A◇A))
   _ = (((A◇A)◇((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B)))◇(((A◇A)◇(A◇A))◇(((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B))◇(A◇A)))) := congrArg (((A◇A)◇((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B)))◇·) ((l88 ((A◇A)) B).symm)
   _ = ((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B)) := l87 A A (((B◇(((A◇A)◇(A◇A))◇(A◇A)))◇((A◇A)◇B))) A
 have l96 : ∀ (B C : G), ((B◇((C◇C)◇C))◇((C◇C)◇B)) = C := by
  intro B C
  have strict_rw_14 := ((l96x C B).symm)
  rw [l89, l90, l5] at strict_rw_14
  exact strict_rw_14
 have l97 : ∀ (B C : G), (((B◇(B◇B))◇C)◇(B◇(C◇(B◇(B◇B))))) = C := by
  intro B C
  calc (((B◇(B◇B))◇C)◇(B◇(C◇(B◇(B◇B)))))
   _ = (((B◇(B◇B))◇C)◇(((B◇(B◇B))◇(B◇(B◇B)))◇(C◇(B◇(B◇B))))) := congrArg (((B◇(B◇B))◇C)◇·) (congrArg (·◇(C◇(B◇(B◇B)))) ((l24 B).symm))
   _ = C := (l3 C ((B◇(B◇B))) ((B◇(B◇B)))).symm
 have l98 : ∀ (B C : G), ((B◇B)◇((((C◇B)◇(B◇C))◇B)◇((C◇B)◇(B◇C)))) = B := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x l24
  clear l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47
  clear l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66 l67
  clear l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88 l89x
  clear l89 l90 l92x l92 l93 l94 l95x l95 l96x l96 l97
  grind
 have l99 : ∀ (B C D : G), ((B◇(C◇(D◇(C◇D))))◇((C◇B)◇(D◇(C◇D)))) = (C◇(D◇(C◇D))) := by
  intro B C D
  calc ((B◇(C◇(D◇(C◇D))))◇((C◇B)◇(D◇(C◇D))))
   _ = ((B◇(C◇(D◇(C◇D))))◇((C◇B)◇((C◇(D◇(C◇D)))◇C))) := congrArg ((B◇(C◇(D◇(C◇D))))◇·) (congrArg ((C◇B)◇·) ((l4 C D).symm))
   _ = (C◇(D◇(C◇D))) := (l3 ((C◇(D◇(C◇D)))) B C).symm
 have l100 : ∀ (B C : G), (B◇((B◇B)◇(((C◇B)◇((B◇B)◇C))◇B))) = (B◇(B◇B)) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l94 l95x l95 l96x l96 l97 l98 l99
  grind
 have l101 : ∀ (B C D : G), (B◇((C◇(((D◇B)◇((B◇B)◇D))◇B))◇((B◇B)◇C))) = (B◇B) := by
  intro B C D
  calc (B◇((C◇(((D◇B)◇((B◇B)◇D))◇B))◇((B◇B)◇C)))
   _ = (((((D◇B)◇((B◇B)◇D))◇B)◇(B◇B))◇((C◇(((D◇B)◇((B◇B)◇D))◇B))◇((B◇B)◇C))) := congrArg (·◇((C◇(((D◇B)◇((B◇B)◇D))◇B))◇((B◇B)◇C))) ((l84 D B).symm)
   _ = (B◇B) := (l3 ((B◇B)) ((((D◇B)◇((B◇B)◇D))◇B)) C).symm
 have l102 : ∀ (B C : G), (((B◇(C◇B))◇(C◇B))◇(C◇(B◇(B◇B)))) = (C◇B) := by
  intro B C
  calc (((B◇(C◇B))◇(C◇B))◇(C◇(B◇(B◇B))))
   _ = (((B◇(C◇B))◇(C◇B))◇(C◇((C◇B)◇(((B◇B)◇B)◇C)))) := congrArg (((B◇(C◇B))◇(C◇B))◇·) (congrArg (C◇·) ((l95 C B).symm))
   _ = (C◇B) := l94 B C ((C◇B))
 have l103 : ∀ (B C : G), (((B◇B)◇B)◇(C◇((B◇B)◇B))) = (((B◇B)◇C)◇B) := by
  intro B C
  calc (((B◇B)◇B)◇(C◇((B◇B)◇B)))
   _ = (((C◇((B◇B)◇B))◇(((B◇B)◇C)◇B))◇(C◇((B◇B)◇B))) := congrArg (·◇(C◇((B◇B)◇B))) ((l12 C B).symm)
   _ = (((C◇((B◇B)◇B))◇(((B◇B)◇C)◇((C◇((B◇B)◇B))◇((B◇B)◇C))))◇(C◇((B◇B)◇B))) := congrArg (·◇(C◇((B◇B)◇B))) (congrArg ((C◇((B◇B)◇B))◇·) (congrArg (((B◇B)◇C)◇·) ((l96 C B).symm)))
   _ = (((B◇B)◇C)◇((C◇((B◇B)◇B))◇((B◇B)◇C))) := ((l4 ((C◇((B◇B)◇B))) (((B◇B)◇C))).symm).symm
   _ = (((B◇B)◇C)◇B) := congrArg (((B◇B)◇C)◇·) (((l96 C B).symm).symm)
 have l104x : ∀ (A B C : G), (((A◇B)◇(B◇A))◇(B◇((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B)))) = (B◇(B◇B)) := by
  intro A B C
  calc (((A◇B)◇(B◇A))◇(B◇((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B))))
   _ = ((((B◇B)◇B)◇(B◇(B◇B)))◇(B◇((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B)))) := congrArg (·◇(B◇((B◇(B◇B))◇(((C◇B)◇(B◇C))◇B)))) ((l75 ((B◇B)) B A).symm)
   _ = (B◇(B◇B)) := l39 B ((B◇(B◇B))) C
 have l104 : ∀ (B C D : G), (((B◇C)◇(C◇B))◇((D◇C)◇(C◇D))) = (C◇(C◇C)) := by
  intro B C D
  have strict_rw_15 := (l104x B C D)
  rw [l30] at strict_rw_15
  exact strict_rw_15
 have l105 : ∀ (B C : G), ((B◇(B◇B))◇((C◇B)◇(B◇C))) = ((B◇B)◇B) := by
  intro B C
  calc ((B◇(B◇B))◇((C◇B)◇(B◇C)))
   _ = (((B◇(B◇B))◇((B◇B)◇B))◇((C◇B)◇(B◇C))) := congrArg (·◇((C◇B)◇(B◇C))) ((l71 B).symm)
   _ = (((B◇(B◇B))◇((B◇B)◇B))◇(B◇((C◇B)◇(B◇C)))) := congrArg (((B◇(B◇B))◇((B◇B)◇B))◇·) ((l66 B C).symm)
   _ = (((B◇(B◇B))◇((B◇B)◇B))◇(B◇(((B◇B)◇B)◇(B◇(B◇B))))) := congrArg (((B◇(B◇B))◇((B◇B)◇B))◇·) (congrArg (B◇·) ((l75 ((B◇B)) B C).symm))
   _ = ((B◇B)◇B) := ((l97 B (((B◇B)◇B))).symm).symm
 have l106x : ∀ (A B : G), (((A◇(B◇(A◇B)))◇(A◇(B◇(A◇B))))◇(((A◇(B◇(A◇B)))◇(A◇(B◇(A◇B))))◇(((B◇(A◇B))◇(A◇(B◇(A◇B))))◇((A◇(B◇(A◇B)))◇(B◇(A◇B)))))) = (A◇(B◇(A◇B))) := by
  intro A B
  calc (((A◇(B◇(A◇B)))◇(A◇(B◇(A◇B))))◇(((A◇(B◇(A◇B)))◇(A◇(B◇(A◇B))))◇(((B◇(A◇B))◇(A◇(B◇(A◇B))))◇((A◇(B◇(A◇B)))◇(B◇(A◇B))))))
   _ = (((A◇(B◇(A◇B)))◇(A◇(B◇(A◇B))))◇(((((B◇(A◇B))◇(A◇(B◇(A◇B))))◇((A◇(B◇(A◇B)))◇(B◇(A◇B))))◇(A◇(B◇(A◇B))))◇(((B◇(A◇B))◇(A◇(B◇(A◇B))))◇((A◇(B◇(A◇B)))◇(B◇(A◇B)))))) := congrArg (((A◇(B◇(A◇B)))◇(A◇(B◇(A◇B))))◇·) (congrArg (·◇(((B◇(A◇B))◇(A◇(B◇(A◇B))))◇((A◇(B◇(A◇B)))◇(B◇(A◇B))))) (congrArg (·◇(A◇(B◇(A◇B)))) ((l99 ((B◇(A◇B))) A B).symm)))
   _ = (A◇(B◇(A◇B))) := l98 ((A◇(B◇(A◇B)))) ((B◇(A◇B)))
 have l106 : ∀ (B C : G), ((B◇(C◇(B◇C)))◇(B◇(C◇(B◇C)))) = (B◇(C◇(B◇C))) := by
  intro B C
  have strict_rw_16 := (l106x B C)
  rw [l99, l51] at strict_rw_16
  exact strict_rw_16
 have l107 : ∀ (B C D : G), ((B◇C)◇(((D◇B)◇(B◇D))◇(C◇(B◇(B◇B))))) = C := by
  intro B C D
  calc ((B◇C)◇(((D◇B)◇(B◇D))◇(C◇(B◇(B◇B)))))
   _ = ((B◇C)◇(((B◇B)◇(B◇B))◇(C◇(B◇(B◇B))))) := congrArg ((B◇C)◇·) (congrArg (·◇(C◇(B◇(B◇B)))) ((l75 B B D).symm))
   _ = C := l44 B C
 have l108x : ∀ (A B C : G), ((A◇(A◇A))◇(A◇(((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A))◇(((C◇A)◇(((A◇A)◇A)◇C))◇A)))) = ((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A)) := by
  intro A B C
  calc ((A◇(A◇A))◇(A◇(((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A))◇(((C◇A)◇(((A◇A)◇A)◇C))◇A))))
   _ = ((A◇((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A)))◇(A◇(((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A))◇(((C◇A)◇(((A◇A)◇A)◇C))◇A)))) := congrArg (·◇(A◇(((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A))◇(((C◇A)◇(((A◇A)◇A)◇C))◇A)))) ((l100 A B).symm)
   _ = ((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A)) := l19 A (((A◇A)◇(((B◇A)◇((A◇A)◇B))◇A))) C
 have l108 : ∀ (B C : G), ((B◇B)◇(((C◇B)◇((B◇B)◇C))◇B)) = (B◇B) := by
  intro B C
  have strict_rw_17 := ((l108x B C B).symm)
  rw [l95, l36, l101, l37] at strict_rw_17
  exact strict_rw_17
 have l109 : ∀ (B C : G), ((B◇(B◇B))◇((((C◇B)◇((B◇B)◇C))◇B)◇B)) = B := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47
  clear l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66 l67
  clear l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l85 l86 l87 l88 l89x l89
  clear l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l103 l104x l104 l105 l106 l107 l108x l108
  grind
 have l110 : ∀ (B C D : G), (((B◇(B◇B))◇C)◇((D◇B)◇(B◇D))) = (((B◇B)◇C)◇B) := by
  intro B C D
  calc (((B◇(B◇B))◇C)◇((D◇B)◇(B◇D)))
   _ = (((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇C)◇((D◇B)◇(B◇D))) := congrArg (·◇((D◇B)◇(B◇D))) (congrArg (·◇C) ((l104 D B D).symm))
   _ = (((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇((D◇B)◇(B◇D)))◇(C◇((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇((D◇B)◇(B◇D))))) := (l103 (((D◇B)◇(B◇D))) C).symm
   _ = (((B◇(B◇B))◇((D◇B)◇(B◇D)))◇(C◇((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇((D◇B)◇(B◇D))))) := congrArg (·◇(C◇((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇((D◇B)◇(B◇D))))) (congrArg (·◇((D◇B)◇(B◇D))) (l104 D B D))
   _ = (((B◇B)◇B)◇(C◇((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇((D◇B)◇(B◇D))))) := congrArg (·◇(C◇((((D◇B)◇(B◇D))◇((D◇B)◇(B◇D)))◇((D◇B)◇(B◇D))))) (l105 B D)
   _ = (((B◇B)◇B)◇(C◇((B◇(B◇B))◇((D◇B)◇(B◇D))))) := congrArg (((B◇B)◇B)◇·) (congrArg (C◇·) (congrArg (·◇((D◇B)◇(B◇D))) (((l104 D B D).symm).symm)))
   _ = (((B◇B)◇B)◇(C◇((B◇B)◇B))) := congrArg (((B◇B)◇B)◇·) (congrArg (C◇·) (((l105 B D).symm).symm))
   _ = (((B◇B)◇C)◇B) := ((l103 B C).symm).symm
 have l111 : ∀ (B C : G), ((B◇(C◇B))◇((C◇(B◇(C◇B)))◇(C◇(C◇(B◇(C◇B)))))) = C := by
  intro B C
  calc ((B◇(C◇B))◇((C◇(B◇(C◇B)))◇(C◇(C◇(B◇(C◇B))))))
   _ = ((B◇(C◇B))◇(((C◇(B◇(C◇B)))◇(C◇(B◇(C◇B))))◇(C◇(C◇(B◇(C◇B)))))) := congrArg ((B◇(C◇B))◇·) (congrArg (·◇(C◇(C◇(B◇(C◇B))))) ((l106 C B).symm))
   _ = C := l18 B C ((C◇(B◇(C◇B))))
 have l112 : ∀ (B C : G), (((B◇C)◇((C◇C)◇B))◇C) = ((C◇C)◇C) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l108x l110
  clear l111
  grind
 have l113 : ∀ (B C : G), (((B◇B)◇((C◇B)◇((B◇B)◇C)))◇B) = B := by
  intro B C
  calc (((B◇B)◇((C◇B)◇((B◇B)◇C)))◇B)
   _ = (((B◇(B◇B))◇((C◇B)◇((B◇B)◇C)))◇((B◇B)◇(B◇B))) := (l110 B (((C◇B)◇((B◇B)◇C))) B).symm
   _ = ((B◇B)◇((B◇B)◇(B◇B))) := congrArg (·◇((B◇B)◇(B◇B))) ((l3 ((B◇B)) B C).symm)
   _ = B := (l3 B B B).symm
 have l114 : ∀ (B C : G), ((((B◇B)◇B)◇C)◇(((B◇B)◇B)◇(C◇((B◇B)◇B)))) = C := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66 l67
  clear l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88 l89x
  clear l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107 l108x
  clear l108 l109 l110 l111 l112 l113
  grind
 have l115 : ∀ (B C D : G), (((((B◇B)◇B)◇(C◇B))◇D)◇(C◇(D◇((B◇(B◇B))◇C)))) = D := by
  intro B C D
  calc (((((B◇B)◇B)◇(C◇B))◇D)◇(C◇(D◇((B◇(B◇B))◇C))))
   _ = ((((B◇(B◇(B◇B)))◇(C◇B))◇D)◇(C◇(D◇((B◇(B◇B))◇C)))) := congrArg (·◇(C◇(D◇((B◇(B◇B))◇C)))) (congrArg (·◇D) (congrArg (·◇(C◇B)) ((l25 B).symm)))
   _ = D := l6 B ((B◇(B◇B))) C D
 have l116 : ∀ (B C : G), ((B◇C)◇((C◇C)◇B)) = (C◇C) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l104x l104 l105 l106 l107 l108x
  clear l108 l109 l110 l114 l115
  grind
 have l117 : ∀ (B C : G), ((((B◇B)◇B)◇C)◇(((B◇B)◇C)◇B)) = C := by
  intro B C
  calc ((((B◇B)◇B)◇C)◇(((B◇B)◇C)◇B))
   _ = ((((B◇B)◇B)◇C)◇(((B◇B)◇B)◇(C◇((B◇B)◇B)))) := congrArg ((((B◇B)◇B)◇C)◇·) ((l103 B C).symm)
   _ = C := l114 B C
 have l118x : ∀ (A B : G), (((((A◇A)◇A)◇(B◇A))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇(B◇((A◇(A◇A))◇(A◇(A◇A))))) = (B◇((A◇(A◇A))◇(A◇(A◇A)))) := by
  intro A B
  calc (((((A◇A)◇A)◇(B◇A))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))
   _ = (((((A◇A)◇A)◇(B◇A))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇(B◇((B◇((A◇(A◇A))◇(A◇(A◇A))))◇((A◇(A◇A))◇B)))) := congrArg (((((A◇A)◇A)◇(B◇A))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))◇·) (congrArg (B◇·) ((l37 B ((A◇(A◇A)))).symm))
   _ = (B◇((A◇(A◇A))◇(A◇(A◇A)))) := l115 A B ((B◇((A◇(A◇A))◇(A◇(A◇A)))))
 have l118 : ∀ (B C : G), (((((B◇B)◇B)◇(C◇B))◇(C◇B))◇(C◇B)) = (C◇B) := by
  intro B C
  have strict_rw_18 := (l118x B C)
  rw [l24] at strict_rw_18
  exact strict_rw_18
 have l119 : ∀ (B C : G), ((B◇(C◇(C◇C)))◇(C◇B)) = C := by
  intro B C
  calc ((B◇(C◇(C◇C)))◇(C◇B))
   _ = ((B◇(((C◇C)◇C)◇C))◇(C◇B)) := congrArg (·◇(C◇B)) (congrArg (B◇·) ((l27 C).symm))
   _ = ((B◇(((C◇C)◇C)◇C))◇(((((C◇C)◇C)◇C)◇(((C◇C)◇C)◇C))◇B)) := congrArg ((B◇(((C◇C)◇C)◇C))◇·) (congrArg (·◇B) ((l117 C C).symm))
   _ = ((((C◇C)◇C)◇C)◇(((C◇C)◇C)◇C)) := ((l116 B ((((C◇C)◇C)◇C))).symm).symm
   _ = C := ((l117 C C).symm).symm
 have l120 : ∀ (B C : G), ((((((B◇C)◇(B◇C))◇(B◇C))◇B)◇B)◇B) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65
  clear l66 l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87
  clear l88 l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106
  clear l107 l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x
  grind
 have l121 : ∀ (B C : G), (((B◇(C◇B))◇C)◇C) = C := by
  intro B C
  clear h l3 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l107 l108x
  clear l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119
  grind
 have l122 : ∀ (B C D : G), ((B◇(C◇(D◇D)))◇(((D◇C)◇B)◇(D◇D))) = (C◇(D◇D)) := by
  intro B C D
  calc ((B◇(C◇(D◇D)))◇(((D◇C)◇B)◇(D◇D)))
   _ = ((B◇(C◇(D◇D)))◇(((D◇C)◇B)◇((C◇(D◇D))◇(D◇C)))) := congrArg ((B◇(C◇(D◇D)))◇·) (congrArg (((D◇C)◇B)◇·) ((l37 C D).symm))
   _ = (C◇(D◇D)) := (l3 ((C◇(D◇D))) B ((D◇C))).symm
 have l123 : ∀ (B C D : G), (B◇((C◇((D◇(B◇D))◇B))◇(B◇C))) = B := by
  intro B C D
  calc (B◇((C◇((D◇(B◇D))◇B))◇(B◇C)))
   _ = ((((D◇(B◇D))◇B)◇B)◇((C◇((D◇(B◇D))◇B))◇(B◇C))) := congrArg (·◇((C◇((D◇(B◇D))◇B))◇(B◇C))) ((l121 D B).symm)
   _ = B := (l3 B (((D◇(B◇D))◇B)) C).symm
 have l124 : ∀ (B C : G), ((B◇(B◇((C◇(B◇C))◇B)))◇B) = B := by
  intro B C
  calc ((B◇(B◇((C◇(B◇C))◇B)))◇B)
   _ = (((((C◇(B◇C))◇B)◇B)◇(B◇((C◇(B◇C))◇B)))◇B) := congrArg (·◇B) (congrArg (·◇(B◇((C◇(B◇C))◇B))) ((l121 C B).symm))
   _ = B := l59 (((C◇(B◇C))◇B)) B
 have l125x : ∀ (A B : G), (A◇(((A◇(A◇((B◇(A◇B))◇A)))◇A)◇(A◇A))) = ((A◇((B◇(A◇B))◇A))◇(A◇A)) := by
  intro A B
  calc (A◇(((A◇(A◇((B◇(A◇B))◇A)))◇A)◇(A◇A)))
   _ = ((A◇((A◇((B◇(A◇B))◇A))◇(A◇A)))◇(((A◇(A◇((B◇(A◇B))◇A)))◇A)◇(A◇A))) := congrArg (·◇(((A◇(A◇((B◇(A◇B))◇A)))◇A)◇(A◇A))) ((l123 A A B).symm)
   _ = ((A◇((B◇(A◇B))◇A))◇(A◇A)) := l122 A ((A◇((B◇(A◇B))◇A))) A
 have l125 : ∀ (B C : G), ((B◇((C◇(B◇C))◇B))◇(B◇B)) = ((B◇B)◇B) := by
  intro B C
  have strict_rw_19 := ((l125x B C).symm)
  rw [l124, l25] at strict_rw_19
  exact strict_rw_19
 have l126 : ∀ (B C : G), ((B◇B)◇(B◇((C◇(B◇C))◇B))) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107
  clear l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l125x l125
  grind
 have l127 : ∀ (B C : G), ((B◇((C◇(B◇C))◇B))◇B) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l67
  clear l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88 l89x
  clear l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107 l108x
  clear l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x
  grind
 have l128 : ∀ (B C : G), (((((B◇B)◇C)◇B)◇C)◇C) = C := by
  intro B C
  calc (((((B◇B)◇C)◇B)◇C)◇C)
   _ = (((((B◇B)◇B)◇(C◇((B◇B)◇B)))◇C)◇C) := congrArg (·◇C) (congrArg (·◇C) ((l103 B C).symm))
   _ = C := l121 (((B◇B)◇B)) C
 have l129 : ∀ (B C : G), ((B◇B)◇((C◇(B◇C))◇B)) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107
  clear l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l128
  grind
 have l130 : ∀ (B C : G), (B◇((C◇(B◇C))◇B)) = ((C◇(B◇C))◇B) := by
  intro B C
  calc (B◇((C◇(B◇C))◇B))
   _ = (((B◇B)◇((C◇(B◇C))◇B))◇((C◇(B◇C))◇B)) := congrArg (·◇((C◇(B◇C))◇B)) ((l129 B C).symm)
   _ = (((((B◇B)◇((C◇(B◇C))◇B))◇B)◇((C◇(B◇C))◇B))◇((C◇(B◇C))◇B)) := congrArg (·◇((C◇(B◇C))◇B)) (congrArg (·◇((C◇(B◇C))◇B)) (congrArg (·◇B) ((l129 B C).symm)))
   _ = ((C◇(B◇C))◇B) := ((l128 B (((C◇(B◇C))◇B))).symm).symm
 have l131x : ∀ (A B C : G), (((A◇(B◇(A◇B)))◇(A◇A))◇(((C◇A)◇(A◇C))◇A)) = (A◇A) := by
  intro A B C
  calc (((A◇(B◇(A◇B)))◇(A◇A))◇(((C◇A)◇(A◇C))◇A))
   _ = (((A◇(B◇(A◇B)))◇(A◇A))◇(((C◇A)◇(A◇C))◇((A◇A)◇((B◇(A◇B))◇A)))) := congrArg (((A◇(B◇(A◇B)))◇(A◇A))◇·) (congrArg (((C◇A)◇(A◇C))◇·) ((l129 A B).symm))
   _ = (A◇A) := l87 A ((B◇(A◇B))) ((A◇A)) C
 have l131 : ∀ (B C : G), (((B◇(C◇(B◇C)))◇(B◇B))◇B) = (B◇B) := by
  intro B C
  have strict_rw_20 := (l131x B C B)
  rw [l59] at strict_rw_20
  exact strict_rw_20
 have l132 : ∀ (B C : G), (((B◇(C◇B))◇C)◇(C◇C)) = ((C◇C)◇C) := by
  intro B C
  calc (((B◇(C◇B))◇C)◇(C◇C))
   _ = ((C◇((B◇(C◇B))◇C))◇(C◇C)) := congrArg (·◇(C◇C)) ((l130 C B).symm)
   _ = ((C◇C)◇C) := l125 C B
 have l133 : ∀ (B C D : G), ((B◇((C◇D)◇(D◇C)))◇(((C◇D)◇(D◇C))◇B)) = D := by
  intro B C D
  calc ((B◇((C◇D)◇(D◇C)))◇(((C◇D)◇(D◇C))◇B))
   _ = ((D◇((C◇D)◇(D◇C)))◇(((C◇D)◇(D◇C))◇D)) := l75 B (((C◇D)◇(D◇C))) D
   _ = ((D◇((C◇D)◇(D◇C)))◇D) := congrArg ((D◇((C◇D)◇(D◇C)))◇·) (l59 C D)
   _ = (((C◇D)◇(D◇C))◇D) := congrArg (·◇D) (((l66 D C).symm).symm)
   _ = D := ((l59 C D).symm).symm
 have l134 : ∀ (B C : G), ((B◇B)◇((C◇(B◇B))◇(((B◇B)◇B)◇C))) = ((B◇B)◇B) := by
  intro B C
  calc ((B◇B)◇((C◇(B◇B))◇(((B◇B)◇B)◇C)))
   _ = (((B◇B)◇((B◇B)◇B))◇((C◇(B◇B))◇(((B◇B)◇B)◇C))) := congrArg (·◇((C◇(B◇B))◇(((B◇B)◇B)◇C))) ((l51 B).symm)
   _ = ((B◇B)◇B) := (l3 (((B◇B)◇B)) ((B◇B)) C).symm
 have l135 : ∀ (B C : G), ((B◇(C◇(B◇C)))◇(B◇B)) = B := by
  intro B C
  calc ((B◇(C◇(B◇C)))◇(B◇B))
   _ = (B◇((B◇((C◇(B◇C))◇B))◇(((B◇(C◇(B◇C)))◇(B◇B))◇B))) := (l30 B B ((C◇(B◇C))) B).symm
   _ = (B◇(((C◇(B◇C))◇B)◇(((B◇(C◇(B◇C)))◇(B◇B))◇B))) := congrArg (B◇·) (congrArg (·◇(((B◇(C◇(B◇C)))◇(B◇B))◇B)) (l130 B C))
   _ = (B◇(((C◇(B◇C))◇B)◇(B◇B))) := congrArg (B◇·) (congrArg (((C◇(B◇C))◇B)◇·) (l131 B C))
   _ = (B◇((B◇B)◇B)) := congrArg (B◇·) (((l132 C B).symm).symm)
   _ = B := ((l17 B).symm).symm
 have l136 : ∀ (B C : G), ((B◇C)◇(B◇(B◇B))) = (((B◇B)◇C)◇B) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l104x l105 l106x l106 l107 l108x
  clear l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128 l129
  clear l130 l131x l131 l132 l134 l135
  have p15x : ∀ (A B : G), (A◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))) = ((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))))) := by
   intro A B
   calc (A◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B))))
    _ = (((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B))))◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))) := congrArg (·◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))) ((l133 (((B◇A)◇(A◇B))) B A).symm)
    _ = ((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))◇(((B◇A)◇(A◇B))◇((B◇A)◇(A◇B)))))) := (l25 ((((B◇A)◇(A◇B))◇((B◇A)◇(A◇B))))).symm
  have p15 : ∀ (X : G),
    ((X◇(X◇X))◇((X◇(X◇X))◇((X◇(X◇X))◇(X◇(X◇X))))) =
     (X◇(X◇(X◇X))) := by
   intro X
   have strict_rw_21 := ((p15x X X).symm)
   rw [l104] at strict_rw_21
   exact strict_rw_21
  grind
 have l137x : ∀ (A B : G), (((A◇A)◇((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B)))◇(A◇A)) = ((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B)) := by
  intro A B
  calc (((A◇A)◇((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B)))◇(A◇A))
   _ = (((A◇A)◇((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B)))◇(((A◇A)◇(A◇A))◇(((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B))◇(A◇A)))) := congrArg (((A◇A)◇((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B)))◇·) ((l85 ((A◇A)) B).symm)
   _ = ((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B)) := l87 A A (((B◇(A◇A))◇((((A◇A)◇(A◇A))◇(A◇A))◇B))) A
 have l137 : ∀ (B C : G), ((B◇(C◇C))◇(((C◇C)◇C)◇B)) = C := by
  intro B C
  have strict_rw_22 := ((l137x C B).symm)
  rw [l89, l134, l5] at strict_rw_22
  exact strict_rw_22
 have l138 : ∀ (B C : G), ((B◇(B◇B))◇(C◇(B◇C))) = B := by
  intro B C
  clear h l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x l24
  clear l25 l26 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47 l48
  clear l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66 l67 l68
  clear l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88 l89x l89
  clear l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l103 l104x l104 l105 l106 l107 l108x l108 l109
  clear l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128 l129 l130 l131x
  clear l131 l132 l133 l134 l136 l137x l137
  grind
 have l139x : ∀ (A B : G), ((A◇A)◇(A◇(((B◇((A◇A)◇B))◇(A◇A))◇(A◇A)))) = ((B◇((A◇A)◇B))◇(A◇A)) := by
  intro A B
  calc ((A◇A)◇(A◇(((B◇((A◇A)◇B))◇(A◇A))◇(A◇A))))
   _ = ((((A◇A)◇(A◇A))◇((B◇((A◇A)◇B))◇(A◇A)))◇(A◇(((B◇((A◇A)◇B))◇(A◇A))◇(A◇A)))) := congrArg (·◇(A◇(((B◇((A◇A)◇B))◇(A◇A))◇(A◇A)))) ((l129 ((A◇A)) B).symm)
   _ = ((B◇((A◇A)◇B))◇(A◇A)) := l6 A A A (((B◇((A◇A)◇B))◇(A◇A)))
 have l139 : ∀ (B C : G), ((B◇((C◇C)◇B))◇(C◇C)) = (C◇(C◇C)) := by
  intro B C
  have strict_rw_23 := ((l139x C B).symm)
  rw [l121, l136, l27] at strict_rw_23
  exact strict_rw_23
 have l140 : ∀ (B C : G), (((((B◇B)◇B)◇(B◇C))◇(C◇B))◇(B◇B)) = (C◇B) := by
  intro B C
  calc (((((B◇B)◇B)◇(B◇C))◇(C◇B))◇(B◇B))
   _ = (((((B◇B)◇B)◇(B◇C))◇(C◇B))◇((((B◇C)◇(B◇B))◇(((B◇B)◇B)◇(B◇C)))◇B)) := congrArg (((((B◇B)◇B)◇(B◇C))◇(C◇B))◇·) (congrArg (·◇B) ((l137 ((B◇C)) B).symm))
   _ = (C◇B) := l11 ((((B◇B)◇B)◇(B◇C))) C B B
 have l141 : ∀ (B C : G), (B◇(C◇((B◇B)◇C))) = (B◇B) := by
  intro B C
  calc (B◇(C◇((B◇B)◇C)))
   _ = (((B◇B)◇((B◇B)◇(B◇B)))◇(C◇((B◇B)◇C))) := congrArg (·◇(C◇((B◇B)◇C))) (((l3 B B B).symm).symm)
   _ = (B◇B) := l138 ((B◇B)) C
 have l142 : ∀ (B C : G), (B◇((C◇((B◇B)◇C))◇B)) = (B◇(B◇B)) := by
  intro B C
  clear h l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47
  clear l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l60x l60 l61x l61 l62 l63 l64 l65 l66 l67 l68
  clear l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88 l89x l89
  clear l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l103 l104x l104 l105 l106 l107 l108x l108 l109
  clear l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128 l129 l130 l131x
  clear l131 l132 l133 l134 l135 l137x l137 l138 l139x l140 l141
  grind
 have l143 : ∀ (B C : G), ((B◇((C◇C)◇B))◇C) = (C◇C) := by
  intro B C
  calc ((B◇((C◇C)◇B))◇C)
   _ = (((((C◇C)◇C)◇(C◇(B◇((C◇C)◇B))))◇((B◇((C◇C)◇B))◇C))◇(C◇C)) := (l140 C ((B◇((C◇C)◇B)))).symm
   _ = (((((C◇C)◇C)◇(C◇C))◇((B◇((C◇C)◇B))◇C))◇(C◇C)) := congrArg (·◇(C◇C)) (congrArg (·◇((B◇((C◇C)◇B))◇C)) (congrArg (((C◇C)◇C)◇·) (l141 C B)))
   _ = ((C◇((B◇((C◇C)◇B))◇C))◇(C◇C)) := congrArg (·◇(C◇C)) (congrArg (·◇((B◇((C◇C)◇B))◇C)) (l5 C))
   _ = ((C◇(C◇C))◇(C◇C)) := congrArg (·◇(C◇C)) (((l142 C B).symm).symm)
   _ = (C◇C) := ((l37 C C).symm).symm
 have l144 : ∀ (B C : G), (B◇((C◇C)◇B)) = C := by
  intro B C
  calc (B◇((C◇C)◇B))
   _ = ((C◇(B◇((C◇C)◇B)))◇((C◇C)◇((B◇((C◇C)◇B))◇C))) := l3 ((B◇((C◇C)◇B))) C C
   _ = ((C◇(B◇((C◇C)◇B)))◇((C◇C)◇(C◇C))) := congrArg ((C◇(B◇((C◇C)◇B)))◇·) (congrArg ((C◇C)◇·) (l143 B C))
   _ = ((C◇C)◇((C◇C)◇(C◇C))) := congrArg (·◇((C◇C)◇(C◇C))) (((l141 C B).symm).symm)
   _ = C := (l3 C C C).symm
 have l145 : ∀ (B C : G), (((B◇B)◇(C◇C))◇B) = C := by
  intro B C
  calc (((B◇B)◇(C◇C))◇B)
   _ = (((B◇B)◇(C◇C))◇((C◇C)◇((B◇B)◇(C◇C)))) := congrArg (((B◇B)◇(C◇C))◇·) ((l144 ((C◇C)) B).symm)
   _ = C := l144 (((B◇B)◇(C◇C))) C
 have l146 : ∀ (B C : G), (((B◇(C◇B))◇(C◇(B◇B)))◇(C◇B)) = (C◇(B◇B)) := by
  intro B C
  calc (((B◇(C◇B))◇(C◇(B◇B)))◇(C◇B))
   _ = (((B◇(C◇B))◇(C◇(B◇B)))◇(C◇((C◇(B◇B))◇(((B◇B)◇B)◇C)))) := congrArg (((B◇(C◇B))◇(C◇(B◇B)))◇·) (congrArg (C◇·) ((l137 C B).symm))
   _ = (C◇(B◇B)) := l94 B C ((C◇(B◇B)))
 have l147x : ∀ (A B : G), (A◇(B◇(((B◇(B◇B))◇(B◇(B◇B)))◇(A◇A)))) = B := by
  intro A B
  calc (A◇(B◇(((B◇(B◇B))◇(B◇(B◇B)))◇(A◇A))))
   _ = (((((B◇(B◇B))◇(B◇(B◇B)))◇(A◇A))◇(B◇(B◇B)))◇(B◇(((B◇(B◇B))◇(B◇(B◇B)))◇(A◇A)))) := congrArg (·◇(B◇(((B◇(B◇B))◇(B◇(B◇B)))◇(A◇A)))) ((l145 ((B◇(B◇B))) A).symm)
   _ = B := l119 ((((B◇(B◇B))◇(B◇(B◇B)))◇(A◇A))) B
 have l147 : ∀ (B C : G), (B◇(C◇(C◇(B◇B)))) = C := by
  intro B C
  have strict_rw_24 := (l147x B C)
  rw [l136, l59] at strict_rw_24
  exact strict_rw_24
 have l148 : ∀ (B C : G), ((B◇(C◇B))◇(B◇(C◇B))) = C := by
  intro B C
  clear h l3 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107
  clear l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128
  clear l129 l130 l131x l131 l132 l133 l134 l136 l137x l137 l138 l139x l139 l140 l141 l142 l143 l144 l145 l147x l147
  grind
 have l149x : ∀ (A B : G), (((A◇(A◇((B◇(B◇B))◇(B◇(B◇B)))))◇B)◇A) = B := by
  intro A B
  calc (((A◇(A◇((B◇(B◇B))◇(B◇(B◇B)))))◇B)◇A)
   _ = (((A◇(A◇((B◇(B◇B))◇(B◇(B◇B)))))◇B)◇((B◇(B◇B))◇(A◇(A◇((B◇(B◇B))◇(B◇(B◇B))))))) := congrArg (((A◇(A◇((B◇(B◇B))◇(B◇(B◇B)))))◇B)◇·) ((l147 ((B◇(B◇B))) A).symm)
   _ = B := l41 ((A◇(A◇((B◇(B◇B))◇(B◇(B◇B)))))) B
 have l149 : ∀ (B C : G), (((B◇(B◇C))◇C)◇B) = C := by
  intro B C
  have strict_rw_25 := (l149x B C)
  rw [l24] at strict_rw_25
  exact strict_rw_25
 have l150 : ∀ (B C : G), ((B◇(B◇C))◇C) = ((B◇C)◇(B◇C)) := by
  intro B C
  calc ((B◇(B◇C))◇C)
   _ = ((B◇(((B◇(B◇C))◇C)◇B))◇(B◇(((B◇(B◇C))◇C)◇B))) := (l148 B (((B◇(B◇C))◇C))).symm
   _ = ((B◇C)◇(B◇(((B◇(B◇C))◇C)◇B))) := congrArg (·◇(B◇(((B◇(B◇C))◇C)◇B))) (congrArg (B◇·) (l149 B C))
   _ = ((B◇C)◇(B◇C)) := congrArg ((B◇C)◇·) (congrArg (B◇·) (((l149 B C).symm).symm))
 have l151 : ∀ (B C : G), (((B◇C)◇(B◇C))◇B) = C := by
  intro B C
  calc (((B◇C)◇(B◇C))◇B)
   _ = (((B◇(B◇C))◇C)◇B) := congrArg (·◇B) ((l150 B C).symm)
   _ = C := l149 B C
 have l152 : ∀ (B C : G), (B◇(C◇(B◇B))) = ((B◇B)◇C) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107 l108x
  clear l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128 l129
  clear l130 l131x l131 l132 l133 l134 l135 l136 l137x l137 l138 l139x l139 l140 l141 l142 l143 l144 l145 l146 l147x l147 l148 l149x
  clear l149 l150
  grind
 have l153 : ∀ (B C : G), (B◇(C◇B)) = (C◇(C◇C)) := by
  intro B C
  calc (B◇(C◇B))
   _ = (B◇(((((C◇C)◇C)◇C)◇(((C◇C)◇C)◇C))◇B)) := congrArg (B◇·) (congrArg (·◇B) ((l117 C C).symm))
   _ = (((C◇C)◇C)◇C) := l144 B ((((C◇C)◇C)◇C))
   _ = (C◇(C◇C)) := ((l27 C).symm).symm
 have l154x : ∀ (A B : G), (((A◇((A◇(A◇A))◇(A◇(A◇A))))◇B)◇(((A◇(A◇A))◇(A◇(A◇A)))◇B)) = B := by
  intro A B
  calc (((A◇((A◇(A◇A))◇(A◇(A◇A))))◇B)◇(((A◇(A◇A))◇(A◇(A◇A)))◇B))
   _ = (((A◇((A◇(A◇A))◇(A◇(A◇A))))◇B)◇((A◇(A◇A))◇(B◇((A◇(A◇A))◇(A◇(A◇A)))))) := congrArg (((A◇((A◇(A◇A))◇(A◇(A◇A))))◇B)◇·) ((l152 ((A◇(A◇A))) B).symm)
   _ = B := l58 A ((A◇(A◇A))) B
 have l154 : ∀ (B C : G), (((B◇B)◇C)◇(B◇C)) = C := by
  intro B C
  have strict_rw_26 := (l154x B C)
  rw [l136, l59] at strict_rw_26
  exact strict_rw_26
 have l155 : ∀ (B C D : G), (B◇(C◇B)) = (D◇(C◇D)) := by
  intro B C D
  calc (B◇(C◇B))
   _ = (C◇(C◇C)) := ((l153 B C).symm).symm
   _ = (D◇(C◇D)) := (l153 D C).symm
 have l156 : ∀ (B C : G), (B◇((C◇B)◇C)) = C := by
  intro B C
  calc (B◇((C◇B)◇C))
   _ = ((((C◇B)◇(C◇B))◇C)◇((C◇B)◇C)) := congrArg (·◇((C◇B)◇C)) ((l151 C B).symm)
   _ = C := l154 ((C◇B)) C
 have l157 : ∀ (B C D : G), ((B◇C)◇((D◇(C◇D))◇B)) = C := by
  intro B C D
  calc ((B◇C)◇((D◇(C◇D))◇B))
   _ = ((B◇C)◇((C◇(C◇C))◇B)) := congrArg ((B◇C)◇·) (congrArg (·◇B) ((l155 C C D).symm))
   _ = C := l41 B C
 have l158 : ∀ (B C : G), (((B◇C)◇B)◇(B◇C)) = C := by
  intro B C
  calc (((B◇C)◇B)◇(B◇C))
   _ = (((B◇C)◇B)◇((C◇((B◇C)◇B))◇C)) := congrArg (((B◇C)◇B)◇·) (congrArg (·◇C) ((l156 C B).symm))
   _ = C := l156 (((B◇C)◇B)) C
 have l159x : ∀ (A B C : G), (((A◇((B◇(C◇B))◇(B◇(C◇B))))◇C)◇(((B◇(C◇B))◇(B◇(C◇B)))◇A)) = C := by
  intro A B C
  calc (((A◇((B◇(C◇B))◇(B◇(C◇B))))◇C)◇(((B◇(C◇B))◇(B◇(C◇B)))◇A))
   _ = (((A◇((B◇(C◇B))◇(B◇(C◇B))))◇C)◇((B◇(C◇B))◇(A◇((B◇(C◇B))◇(B◇(C◇B)))))) := congrArg (((A◇((B◇(C◇B))◇(B◇(C◇B))))◇C)◇·) ((l152 ((B◇(C◇B))) A).symm)
   _ = C := l157 ((A◇((B◇(C◇B))◇(B◇(C◇B))))) C B
 have l159 : ∀ (B C : G), (((B◇C)◇C)◇(C◇B)) = C := by
  intro B C
  have strict_rw_27 := (l159x B B C)
  rw [l148] at strict_rw_27
  exact strict_rw_27
 have l160 : ∀ (B C : G), ((B◇B)◇C) = ((B◇C)◇B) := by
  intro B C
  calc ((B◇B)◇C)
   _ = (((C◇((B◇C)◇B))◇B)◇C) := congrArg (·◇C) (congrArg (·◇B) ((l156 C B).symm))
   _ = (((C◇((B◇C)◇B))◇(C◇((B◇C)◇B)))◇C) := congrArg (·◇C) (congrArg ((C◇((B◇C)◇B))◇·) ((l156 C B).symm))
   _ = ((B◇C)◇B) := ((l151 C (((B◇C)◇B))).symm).symm
 have l161 : ∀ (B C : G), ((B◇B)◇((C◇B)◇B)) = (B◇C) := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23
  clear l24x l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45
  clear l46 l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65
  clear l66 l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87
  clear l88 l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106
  clear l107 l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127
  clear l128 l129 l130 l131x l131 l132 l133 l134 l135 l136 l137x l137 l138 l139x l139 l140 l141 l142 l143 l144 l145 l146 l147x l147
  clear l148 l149x l149 l150 l151 l152 l153 l154x l154 l155 l156 l157 l159x
  grind
 have l162x : ∀ (A B : G), (((A◇A)◇B)◇(A◇(B◇((A◇A)◇A)))) = (B◇((A◇A)◇A)) := by
  intro A B
  calc (((A◇A)◇B)◇(A◇(B◇((A◇A)◇A))))
   _ = (((A◇A)◇B)◇(((B◇((A◇A)◇A))◇((A◇A)◇B))◇(B◇((A◇A)◇A)))) := congrArg (((A◇A)◇B)◇·) (congrArg (·◇(B◇((A◇A)◇A))) ((l96 B A).symm))
   _ = (B◇((A◇A)◇A)) := l156 (((A◇A)◇B)) ((B◇((A◇A)◇A)))
 have l162 : ∀ (B C : G), (B◇((C◇C)◇C)) = B := by
  intro B C
  have strict_rw_28 := ((l162x C B).symm)
  rw [l7] at strict_rw_28
  exact strict_rw_28
 have l163 : ∀ (B C : G), (B◇(B◇(C◇C))) = ((B◇C)◇B) := by
  intro B C
  calc (B◇(B◇(C◇C)))
   _ = (((C◇(B◇(B◇(C◇C))))◇C)◇(C◇(B◇(B◇(C◇C))))) := (l158 C ((B◇(B◇(C◇C))))).symm
   _ = ((B◇C)◇(C◇(B◇(B◇(C◇C))))) := congrArg (·◇(C◇(B◇(B◇(C◇C))))) (congrArg (·◇C) (l147 C B))
   _ = ((B◇C)◇B) := congrArg ((B◇C)◇·) (((l147 C B).symm).symm)
 have l164 : ∀ (B C : G), ((((B◇B)◇(B◇B))◇C)◇(((B◇B)◇(B◇B))◇(C◇B))) = C := by
  intro B C
  calc ((((B◇B)◇(B◇B))◇C)◇(((B◇B)◇(B◇B))◇(C◇B)))
   _ = ((((B◇B)◇(B◇B))◇C)◇((B◇((B◇B)◇(B◇B)))◇(C◇B))) := congrArg ((((B◇B)◇(B◇B))◇C)◇·) (congrArg (·◇(C◇B)) ((l38 B).symm))
   _ = C := (l3 C (((B◇B)◇(B◇B))) B).symm
 have l165 : ∀ (B C : G), (((B◇C)◇C)◇(C◇C)) = B := by
  intro B C
  clear h l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107
  clear l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128
  clear l129 l130 l131x l131 l132 l133 l134 l135 l136 l137x l137 l138 l139x l139 l140 l141 l142 l143 l144 l145 l146 l147x l147 l148
  clear l149x l149 l150 l151 l153 l154x l154 l155 l156 l157 l159x l160 l162x l164
  grind
 have l166 : ∀ (B C D : G), ((B◇(C◇B))◇(D◇C)) = (C◇D) := by
  intro B C D
  calc ((B◇(C◇B))◇(D◇C))
   _ = ((B◇(C◇B))◇(D◇((B◇(C◇B))◇(B◇(C◇B))))) := congrArg ((B◇(C◇B))◇·) (congrArg (D◇·) ((l148 B C).symm))
   _ = (((B◇(C◇B))◇(B◇(C◇B)))◇D) := l152 ((B◇(C◇B))) D
   _ = (C◇D) := congrArg (·◇D) (((l148 B C).symm).symm)
 have l167x : ∀ (A B : G), (((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇((B◇A)◇A))◇((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇B)) = ((B◇A)◇A) := by
  intro A B
  calc (((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇((B◇A)◇A))◇((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇B))
   _ = (((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇((B◇A)◇A))◇((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇(((B◇A)◇A)◇(A◇A)))) := congrArg (((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇((B◇A)◇A))◇·) (congrArg ((((A◇A)◇(A◇A))◇((A◇A)◇(A◇A)))◇·) ((l165 B A).symm))
   _ = ((B◇A)◇A) := l164 ((A◇A)) (((B◇A)◇A))
 have l167 : ∀ (B C : G), (B◇(C◇(C◇C))) = ((B◇C)◇C) := by
  intro B C
  have strict_rw_29 := (l167x C B)
  rw [l45, l166, l166] at strict_rw_29
  exact strict_rw_29
 have l168 : ∀ (B : G), (((B◇B)◇(B◇B))◇B) = B := by
  intro B
  calc (((B◇B)◇(B◇B))◇B)
   _ = (((B◇B)◇(B◇B))◇((B◇B)◇((B◇B)◇(B◇B)))) := congrArg (((B◇B)◇(B◇B))◇·) (l3 B B B)
   _ = ((B◇B)◇((B◇B)◇(B◇B))) := l31 ((B◇B))
   _ = B := (l3 B B B).symm
 have l169 : ∀ (B C : G), ((B◇(B◇B))◇(C◇B)) = (B◇C) := by
  intro B C
  exact l166 B B C
 have l170 : ∀ (B C : G), (((B◇C)◇C)◇B) = (B◇(B◇C)) := by
  intro B C
  calc (((B◇C)◇C)◇B)
   _ = ((B◇(C◇(C◇C)))◇B) := congrArg (·◇B) ((l167 B C).symm)
   _ = (B◇(B◇((C◇(C◇C))◇(C◇(C◇C))))) := (l163 B ((C◇(C◇C)))).symm
   _ = (B◇(B◇(((C◇(C◇C))◇C)◇C))) := congrArg (B◇·) (congrArg (B◇·) (l167 ((C◇(C◇C))) C))
   _ = (B◇(B◇(((C◇C)◇(C◇C))◇C))) := congrArg (B◇·) (congrArg (B◇·) (congrArg (·◇C) (((l36 C).symm).symm)))
   _ = (B◇(B◇C)) := congrArg (B◇·) (congrArg (B◇·) (((l168 C).symm).symm))
 have l171 : ∀ (B C : G), (((B◇B)◇C)◇B) = (B◇(C◇B)) := by
  intro B C
  calc (((B◇B)◇C)◇B)
   _ = ((B◇C)◇(B◇(B◇B))) := (l136 B C).symm
   _ = (((B◇(B◇B))◇(C◇B))◇(B◇(B◇B))) := congrArg (·◇(B◇(B◇B))) ((l169 B C).symm)
   _ = (((B◇(B◇B))◇(B◇(B◇B)))◇(C◇B)) := (l160 ((B◇(B◇B))) ((C◇B))).symm
   _ = ((((B◇B)◇(B◇B))◇B)◇(C◇B)) := congrArg (·◇(C◇B)) (((l136 B ((B◇B))).symm).symm)
   _ = (B◇(C◇B)) := congrArg (·◇(C◇B)) (((l59 B B).symm).symm)
 have l172 : ∀ (B C : G), (((B◇C)◇B)◇C) = (B◇(B◇C)) := by
  intro B C
  calc (((B◇C)◇B)◇C)
   _ = (((B◇C)◇B)◇(((B◇C)◇B)◇(B◇C))) := congrArg (((B◇C)◇B)◇·) ((l158 B C).symm)
   _ = (((((B◇C)◇B)◇(B◇C))◇(B◇C))◇((B◇C)◇B)) := (l170 (((B◇C)◇B)) ((B◇C))).symm
   _ = ((C◇(B◇C))◇((B◇C)◇B)) := congrArg (·◇((B◇C)◇B)) (congrArg (·◇(B◇C)) (((l158 B C).symm).symm))
   _ = (B◇(B◇C)) := ((l166 C B ((B◇C))).symm).symm
 have l174 : ∀ (B C : G), ((B◇(C◇B))◇(B◇B)) = (B◇C) := by
  intro B C
  calc ((B◇(C◇B))◇(B◇B))
   _ = ((((B◇B)◇C)◇B)◇(B◇B)) := congrArg (·◇(B◇B)) ((l171 B C).symm)
   _ = ((((B◇C)◇B)◇B)◇(B◇B)) := congrArg (·◇(B◇B)) (congrArg (·◇B) (l160 B C))
   _ = (B◇C) := ((l165 ((B◇C)) B).symm).symm
 have l175 : ∀ (B C : G), ((B◇B)◇((C◇C)◇B)) = (C◇B) := by
  intro B C
  calc ((B◇B)◇((C◇C)◇B))
   _ = ((B◇((C◇C)◇B))◇B) := ((l160 B (((C◇C)◇B))).symm).symm
   _ = (C◇B) := congrArg (·◇B) (l144 B C)
 have l176 : ∀ (B C : G), (((B◇B)◇C)◇C) = (B◇(B◇C)) := by
  intro B C
  clear h l3 l4 l5 l6 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22x l22 l23x l23 l24x
  clear l24 l25 l26 l27 l28 l29 l30 l31 l32x l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46
  clear l47 l48 l49 l50 l51 l52 l53x l53 l54 l55x l55 l56 l57 l58 l59 l60x l60 l61x l61 l62 l63 l64 l65 l66
  clear l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78x l78 l79 l80 l81 l82 l83 l84x l84 l85 l86 l87 l88
  clear l89x l89 l90 l91 l92x l92 l93 l94 l95x l95 l96x l96 l97 l98 l99 l100 l101 l102 l103 l104x l104 l105 l106 l107
  clear l108x l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118x l118 l119 l120 l121 l122 l123 l124 l125x l125 l126 l127 l128
  clear l129 l130 l131x l131 l132 l133 l134 l135 l136 l137x l137 l138 l139x l139 l140 l141 l142 l143 l145 l146 l147x l147 l148 l149x
  clear l149 l150 l151 l152 l153 l154x l154 l155 l156 l157 l158 l159x l159 l160 l161 l162x l163 l164 l165 l166 l167x l167 l168 l169
  clear l170 l171 l174 l175
  grind
 have l178 : ∀ (B C D : G), ((((B◇((C◇C)◇C))◇(C◇B))◇D)◇(C◇(D◇(C◇(C◇C))))) = D := by
  intro B C D
  calc ((((B◇((C◇C)◇C))◇(C◇B))◇D)◇(C◇(D◇(C◇(C◇C)))))
   _ = ((((B◇((C◇C)◇C))◇(C◇B))◇D)◇(C◇(D◇(((C◇C)◇C)◇C)))) := congrArg ((((B◇((C◇C)◇C))◇(C◇B))◇D)◇·) (congrArg (C◇·) (congrArg (D◇·) ((l27 C).symm)))
   _ = D := l6 B (((C◇C)◇C)) C D
 have l179 : ∀ (B C : G), (B◇(C◇C)) = (C◇(B◇B)) := by
  intro B C
  calc (B◇(C◇C))
   _ = ((B◇((C◇C)◇B))◇(B◇B)) := (l174 B ((C◇C))).symm
   _ = ((B◇((C◇B)◇C))◇(B◇B)) := congrArg (·◇(B◇B)) (congrArg (B◇·) (l160 C B))
   _ = (C◇(B◇B)) := congrArg (·◇(B◇B)) (((l156 B C).symm).symm)
 have l180 : ∀ (B C : G), (B◇(C◇(C◇B))) = ((C◇B)◇B) := by
  intro B C
  calc (B◇(C◇(C◇B)))
   _ = (B◇(((C◇C)◇B)◇B)) := congrArg (B◇·) ((l176 C B).symm)
   _ = (((B◇B)◇((C◇C)◇B))◇B) := (l171 B (((C◇C)◇B))).symm
   _ = ((C◇B)◇B) := congrArg (·◇B) (((l175 B C).symm).symm)
 have l182x : ∀ (A B C : G), ((A◇(((B◇((C◇C)◇C))◇(C◇B))◇((B◇((C◇C)◇C))◇(C◇B))))◇(C◇((A◇A)◇(C◇(C◇C))))) = (A◇A) := by
  intro A B C
  calc ((A◇(((B◇((C◇C)◇C))◇(C◇B))◇((B◇((C◇C)◇C))◇(C◇B))))◇(C◇((A◇A)◇(C◇(C◇C)))))
   _ = ((((B◇((C◇C)◇C))◇(C◇B))◇(A◇A))◇(C◇((A◇A)◇(C◇(C◇C))))) := congrArg (·◇(C◇((A◇A)◇(C◇(C◇C))))) ((l179 (((B◇((C◇C)◇C))◇(C◇B))) A).symm)
   _ = (A◇A) := l178 B C ((A◇A))
 have l182 : ∀ (B C : G), ((B◇C)◇((B◇C)◇C)) = (B◇B) := by
  intro B C
  have strict_rw_30 := (l182x B B C)
  rw [l162, l148, l167, l176, l180] at strict_rw_30
  exact strict_rw_30
 exact (l182 x y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19023_to_46810 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19023_to_46810
