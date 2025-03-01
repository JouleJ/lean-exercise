namespace Axiomatic.Set

structure SetTheory where
    Set: Type
    inside: Set → Set → Prop

    axComprehensionSufficient: ∀A: Set, ∀B: Set, (∀x: Set, inside x A → inside x B) → (∀x: Set, inside x B → inside x A) → (A = B)

    empty: Set
    axEmpty: ∀A: Set, inside A empty → False

    Pair: Set → Set → Set
    axPairNecessary: ∀x: Set, ∀y: Set, ∀z: Set, (inside z (Pair x y) → (z = x ∨ z = y))
    axPairSufficientLeft: ∀x: Set, ∀y: Set, (inside x (Pair x y))
    axPairSufficientRight: ∀x: Set, ∀y: Set, (inside y (Pair x y))

    unionOfFamily: Set → Set
    axUnionOfFamilyNecessary: ∀F: Set, ∀x: Set, (inside x (unionOfFamily F)) → (∃A: Set, (inside x A ∧ inside A F))
    axUnionOfFamilySufficient: ∀F: Set, ∀A: Set, ∀x: Set, (inside A F → inside x A → inside x (unionOfFamily F))

    separate: Set -> (Set -> Prop) -> Set
    separateNecessaryInside: ∀A: Set, ∀p: (Set → Prop), ∀x: Set, (inside x (separate A p) → inside x A)
    separateNecessaryHasProp: ∀A: Set, ∀p: (Set → Prop), ∀x: Set, (inside x (separate A p) → (p x))
    separateSufficient: ∀A: Set, ∀p: (Set → Prop), ∀x: Set, (inside x A → (p x) → inside x (separate A p))

def inside {st: SetTheory} (x: st.Set) (A: st.Set) : Prop := st.inside x A
infix:80 "∈" => inside

def empty {st: SetTheory} : st.Set := st.empty
notation "∅" => empty

def isPartOf {st: SetTheory} (A: st.Set) (B: st.Set) : Prop := ∀x: st.Set, x ∈ A → x ∈ B
infix:80 "⊆" => isPartOf

def lemmaEmptyIsPartOfAnySet {st: SetTheory} (A: st.Set) : (isPartOf ∅ A)
    := by intro x hInEmpty
          exact False.elim (st.axEmpty x hInEmpty)

def lemmaSetContainingNothingIsEmpty {st: SetTheory} (A: st.Set) (h: (∀x: st.Set, x ∈ A → False)) : (A = empty)
    := by apply st.axComprehensionSufficient A empty
          intro x xInA
          exact False.elim (h x xInA)
          exact (lemmaEmptyIsPartOfAnySet A)

def lemmaUnorderedPairIsSymmetric {st: SetTheory} (x: st.Set) (y: st.Set) : (st.Pair x y = st.Pair y x) 
    := by apply st.axComprehensionSufficient (st.Pair x y) (st.Pair y x)
          intro z zInPair
          cases (st.axPairNecessary x y z zInPair) with
            | inl h => rw [h]; exact (st.axPairSufficientRight y x)
            | inr h => rw [h]; exact (st.axPairSufficientLeft y x)
          intro w wInPair
          cases (st.axPairNecessary y x w wInPair) with
            | inl h => rw [h]; exact (st.axPairSufficientRight x y)
            | inr h => rw [h]; exact (st.axPairSufficientLeft x y)

def singleton {st: SetTheory} (A: st.Set) : st.Set := st.Pair A A
def union {st: SetTheory} (A: st.Set) (B: st.Set) : st.Set := st.unionOfFamily (st.Pair A B)

def lemmaUnionNecessary {st: SetTheory} (A: st.Set) (B: st.Set) : (∀x: st.Set, x ∈ (union A B) → (x ∈ A ∨ x ∈ B))
    := by intro x xInUnion
          cases (st.axUnionOfFamilyNecessary (st.Pair A B) x xInUnion) with
            | intro C h => cases (st.axPairNecessary A B C h.right)  with
                             | inl h' => apply Or.inl; rw [<- h']; exact h.left
                             | inr h' => apply Or.inr; rw [<- h']; exact h.left

def lemmaUnion {st: SetTheory} (F: st.Set) (A: st.Set) : (A ∈ F → A ⊆ (st.unionOfFamily F))
    := by intro AinF
          intro x xInA
          exact st.axUnionOfFamilySufficient F A x AinF xInA

infix:80 "∪" => union

def theoremUnionCommutative {st: SetTheory} (A: st.Set) (B: st.Set) : (union A B = union B A)
    := by have h: (st.unionOfFamily (st.Pair A B) = st.unionOfFamily (st.Pair B A))
            := by rw [lemmaUnorderedPairIsSymmetric A B]
          exact h

def intersectionOfFamily {st: SetTheory} (F: st.Set) : st.Set
    := st.separate (st.unionOfFamily F) (fun x => ∀A: st.Set, (A ∈ F → x ∈ A))

def intersection {st: SetTheory} (A: st.Set) (B: st.Set) : st.Set
    := intersectionOfFamily (st.Pair A B)

def theoremIntersectionCommutative {st: SetTheory} (A: st.Set) (B: st.Set) : (intersection A B = intersection B A)
    := by have h: (intersectionOfFamily (st.Pair A B) = intersectionOfFamily (st.Pair B A))
            := by rw [lemmaUnorderedPairIsSymmetric A B]
          exact h

infix:80 "∩" => intersection
