import «LeanExercise».Set
open Set

structure Group (α: Type) where
  G: Set α
  combine: α → α → α
  inverse: α → α

  closedUnderCombine: ∀g: α, ∀h: α, (inside g G) ∧ (inside h G) → (inside (combine h g) G)
