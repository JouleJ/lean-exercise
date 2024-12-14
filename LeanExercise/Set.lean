namespace Set

-- Set is always collection of elements of same type
structure Set (α: Type) where
    p: α → Prop -- predicate selecting content of the set

def getPredicate {α: Type} (A: Set α): (α → Prop) := match A with
    | Set.mk p => p

def contains {α: Type} (A: Set α): α → Prop := match A with
    | Set.mk p => p

def inside {α: Type} (x: α) (A: Set α): Prop := contains A x

def mkEmptySet {α: Type}: Set α := Set.mk (fun _ => False)

theorem emptySetHasNoElements {α: Type}: ∀x: α, ¬(inside x mkEmptySet)
    := by intro x
          intro hp
          exact hp

def mkSingleton {α: Type}: α → Set α := fun x => Set.mk (fun y => y = x)

def isSubSet {α: Type} (A: Set α) (B: Set α): Prop := ∀x: α, (inside x A) → (inside x B)

theorem setIncludesSingletonsOfItsElements {α: Type} (A: Set α): ∀x: α, inside x A → isSubSet (mkSingleton x) A
  := by intro x xInA
        intro t tinSingleton
        have h: (t = x) := by assumption
        have h': (inside t A) := by rewrite [h]; exact xInA
        exact h'

def mkSubSet {α: Type} (q: α → Prop) (A: Set α): Set α := match A with
    | Set.mk p => Set.mk (fun x => (p x) ∧ (q x))

theorem subSetDefIsCorrect {α: Type}: (∀A: Set α, ∀q: (α → Prop), isSubSet (mkSubSet q A) A)
    := by intro A
          intro q
          intro x
          intro h
          exact h.left

theorem setContainsElementsOfSubset {α: Type} (A: Set α) (B: Set α) (p: isSubSet B A): ∀x: α, inside x B → inside x A
  := by intro x xInB
        apply p
        exact xInB

def intersection (α: Type) (F: Set (Set α)): Set α := Set.mk (fun x => ∀A: Set α, inside x A ∧ inside A F)
def union (α: Type) (F: Set (Set α)): Set α := Set.mk (fun x => ∃A: Set α, inside x A ∧ inside A F)
