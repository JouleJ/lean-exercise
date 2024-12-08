import «LeanExercise».Set
open Set

structure Group (α: Type) where
  G: Set α
  combine: α → α → α
  inverse: α → α
  neutral: α

  combineLiesInG:
    ∀g: α, ∀h: α,
    (inside g G) ∧ (inside h G) → (inside (combine g h) G)
  neutralLiesInG:
    inside neutral G
  inverseLiesInG:
    ∀g: α,
    (inside g G) → (inside (inverse g) G)
  combineIsAssociative:
    ∀g: α, ∀h: α, ∀k: α,
    (inside g G) ∧ (inside h G) ∧ (inside k G) → combine g (combine h k) = combine (combine g h) k
  neutralIsCorrect:
    ∀g: α,
    (inside g G) → combine g neutral = g ∧ combine neutral g = g
  inverseIsCorrect:
    ∀g: α,
    (inside g G) → combine g (inverse g) = neutral ∧ combine (inverse g) g = neutral

theorem leftReduce {α: Type} (G: Group α):
  ∀g: α, ∀h: α, ∀k: α,
  (inside g G.G) ∧ (inside h G.G) ∧ (inside k G.G) → (G.combine g h = G.combine g k) → (h = k)
  := by intro g
        intro h
        intro k
        intro q
        intro p
        calc
          h = G.combine G.neutral h := Eq.symm ((G.neutralIsCorrect h q.right.left).right)
          _ = G.combine (G.combine (G.inverse g) g) h := by rewrite [<- (G.inverseIsCorrect g q.left).right]
                                                            rfl
          _ = G.combine (G.inverse g) (G.combine g h) := by apply Eq.symm
                                                            apply G.combineIsAssociative (G.inverse g) g h
                                                            apply And.intro
                                                            exact (G.inverseLiesInG g q.left)
                                                            apply And.intro
                                                            exact q.left
                                                            exact q.right.left
          _ = G.combine (G.inverse g) (G.combine g k) := by rewrite [p]
                                                            rfl
          _ = G.combine (G.combine (G.inverse g) g) k := by apply G.combineIsAssociative (G.inverse g) g k
                                                            apply And.intro
                                                            exact (G.inverseLiesInG g q.left)
                                                            apply And.intro
                                                            exact q.left
                                                            exact q.right.right
          _ = G.combine G.neutral k := by rewrite [(G.inverseIsCorrect g q.left).right]
                                          rfl
          _ = k := (G.neutralIsCorrect k q.right.right).right

#check leftReduce

theorem sufficientConditionForBeingInverse {α: Type} (G: Group α):
  ∀g: α, ∀h: α,
  (inside g G.G) ∧ (inside h G.G) → (G.combine g h = G.neutral) → (h = G.inverse g)
  := by intro g
        intro h
        intro (And.intro gInG hInG)
        intro p
        have gInvInG: inside (G.inverse g) G.G := G.inverseLiesInG g gInG
        calc
          h = G.combine G.neutral h := Eq.symm ((G.neutralIsCorrect h hInG).right)
          _ = G.combine (G.combine (G.inverse g) g) h := by rewrite [<- (G.inverseIsCorrect g gInG).right]
                                                            rfl
          _ = G.combine (G.inverse g) (G.combine g h)
            := by apply Eq.symm
                  apply G.combineIsAssociative (G.inverse g) g h
                  apply And.intro
                  exact gInvInG
                  apply And.intro
                  exact gInG
                  exact hInG
          _ = G.combine (G.inverse g) G.neutral := by rewrite [p]
                                                      rfl
          _ = G.inverse g := (G.neutralIsCorrect (G.inverse g) gInvInG).left

#check sufficientConditionForBeingInverse

theorem inverseOfProduct {α: Type} (G: Group α):
 ∀g: α, ∀h: α,
  (inside g G.G) ∧ (inside h G.G) → G.inverse (G.combine g h) = G.combine (G.inverse h) (G.inverse g)
  := by intro g
        intro h
        intro (And.intro gInG hInG)
        let gInv: α := G.inverse g
        have gInvEqItself: (gInv = G.inverse g) := by simp
        have gInvInG: (inside gInv G.G) := by rewrite [gInvEqItself]
                                              exact G.inverseLiesInG g gInG
        let hInv: α := G.inverse h
        have hInvEqItself: (hInv = G.inverse h) := by simp
        have hInvInG: (inside hInv G.G) := by rewrite [hInvEqItself]
                                              exact G.inverseLiesInG h hInG
        let a: α := G.combine g h
        have aEqItself: (a = G.combine g h) := by simp
        have aInG: (inside a G.G) := by rewrite [aEqItself]
                                        exact G.combineLiesInG g h (And.intro gInG hInG)
        let b: α := G.combine hInv gInv
        have bEqItself: (b = G.combine hInv gInv) := by simp
        have bInG: (inside b G.G) := by rewrite [bEqItself]
                                        exact G.combineLiesInG hInv gInv (And.intro hInvInG gInvInG)
        apply Eq.symm
        apply sufficientConditionForBeingInverse G a b
        apply And.intro
        exact aInG
        exact bInG
        rewrite [aEqItself]
        calc
          G.combine a b = G.combine (G.combine g h) b := by congr
          _ = G.combine g (G.combine h b) := by apply Eq.symm
                                                apply G.combineIsAssociative g h b
                                                apply And.intro
                                                assumption
                                                apply And.intro
                                                assumption
                                                assumption
          _ = G.combine g (G.combine h (G.combine hInv gInv)) := by congr
          _ = G.combine g (G.combine (G.combine h hInv) gInv) := by congr 1
                                                                    apply G.combineIsAssociative h hInv gInv
                                                                    apply And.intro
                                                                    assumption
                                                                    apply And.intro
                                                                    assumption
                                                                    assumption
          _ = G.combine g (G.combine G.neutral gInv) := by congr
                                                           exact (G.inverseIsCorrect h hInG).left
          _ = G.combine g gInv := by congr
                                     exact (G.neutralIsCorrect gInv gInvInG).right
          _ = G.neutral := (G.inverseIsCorrect g gInG).left

#check inverseOfProduct
