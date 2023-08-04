module exercises where

open import logic
open import sets

th-1 : (x y : 𝕊) → x ⊆ y → (∪ x) ⊆ (∪ y)
th-1 x y (⊆-def z) = ⊆-def λ w i → to (∪-def {w} {y}) (lm-1 w (back (∪-def {w} {x}) i))
    where lm-1 : (a : 𝕊) → ∃ (λ α → a ∈ α and α ∈ x) → ∃ λ α → a ∈ α and α ∈ y
          lm-1 a (∃-def _ b (and-def c d)) = ∃-def (λ α → a ∈ α and α ∈ y) b (and-def c (z b d))

th-2 : (x : 𝕊) → x ⊆ 𝓟 (∪ x)
th-2 x = ⊆-def λ y z → to (𝓟-def {y} {∪ x}) (⊆-def λ w i → to (∪-def {w} {x}) (∃-def (λ j → w ∈ j and j ∈ x) y (and-def i z)))

th-3 : (x : 𝕊) → ∪ x ⊆ x → ∪ (𝓟 x) ⊆ 𝓟 x
th-3 x (⊆-def y) = ⊆-def λ z w → to (𝓟-def {z} {x}) (⊆-def (λ i j → y i (to (∪-def {i} {x}) (∃-def (λ α → i ∈ α and α ∈ x) z (and-def j (lm-1 z (back (∪-def {z} {𝓟 x}) w)))))))
    where lm-1 : (z : 𝕊) → ∃ (λ α → z ∈ α and α ∈ 𝓟 x) → z ∈ x 
          lm-1 z (∃-def _ a (and-def b c)) = ⊆-to ((back (𝓟-def {a} {x})) c) z b

th-4 : (x y : 𝕊) → x ⊆ y ≡ union x y == y
th-4 x y = ≡-def (and-def
                  (λ {(⊆-def z) → ==-def λ w → ≡-def (and-def
                                                      (λ i → to or-idempotency (or-application (back (union-def {x} {y} {w}) i) (z w) id))
                                                      λ i → to (union-def {x} {y} {w}) (or-def-right i))})
                  λ {(==-def j) → ⊆-def λ w i → to (j w) (to (union-def {x} {y} {w}) (or-def-left i))})

th-5 : (x y z w : 𝕊) → ¬(x == ∅) → ¬(y == ∅) → union (x × y) (y × x) == z × w → x == y and y == z and z == w
th-5 x y z w i j (==-def k) = and-def (and-def {!!} {!!}) {!!}
    where lm-1 : union x y == z
          lm-1 = ==-def λ t → {!!}
          lm-2 = λ t → ≡-transitivity (or-replacement (×-def {t} {x} {y}) (×-def {t} {y} {x})) (≡-transitivity (≡-transitivity union-def (k t)) (≡-commutativity ×-def))
          lm-3 = λ t →
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → ∃ λ w''' → ∃ λ w'''' → ∃ λ i''' → ∃ λ i'''' → (w' ∈ z and i' ∈ w and t == tuple w' i')
                                                                                                            and
                                                                                                            ((w' ∈ x and i' ∈ y and t == tuple w'' i'')
                                                                                                             or
                                                                                                             (w' ∈ y and i' ∈ x and t == tuple w'''' i'''')))
                       ≡[ {!!} ]≡
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → ∃ λ w''' → ∃ λ w'''' → ∃ λ i''' → ∃ λ i'''' → ((w' ∈ z and i' ∈ w and t == tuple w' i')
                                                                                                             and
                                                                                                             (w' ∈ x and i' ∈ y and t == tuple w'' i''))
                                                                                                            or
                                                                                                            ((w' ∈ z and i' ∈ w and t == tuple w' i')
                                                                                                             and
                                                                                                             (w' ∈ y and i' ∈ x and t == tuple w'''' i'''')))
                       ≡[ {!!} ]≡
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → ∃ λ w''' → ∃ λ w'''' → ∃ λ i''' → ∃ λ i'''' → ((w' ∈ z and i' ∈ w and t == tuple w' i')
                                                                                                             and
                                                                                                             (w' ∈ x and i' ∈ y and t == tuple w'' i''))
                                                                                                            or
                                                                                                            ((w''' ∈ z and i''' ∈ w and t == tuple w''' i''')
                                                                                                             and
                                                                                                             (w''' ∈ y and i''' ∈ x and t == tuple w'''' i'''')))
                       ≡[ {!!} ]≡
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → (w' ∈ z and i' ∈ w and t == tuple w' i') and (w' ∈ x and i' ∈ y and t == tuple w'' i''))
                       or
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → (w' ∈ z and i' ∈ w and t == tuple w' i') and (w' ∈ y and i' ∈ x and t == tuple w'' i''))
                       ≡[ or-replacement
                          (∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → {!!})
                          (∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → {!!}) ]≡
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → (w' ∈ z and i' ∈ w and t == tuple w' i') and (w'' ∈ x and i'' ∈ y and t == tuple w'' i''))
                       or
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → (w' ∈ z and i' ∈ w and t == tuple w' i') and (w'' ∈ y and i'' ∈ x and t == tuple w'' i''))
                       ≡[ or-replacement (∃-replacement λ _ → ∃-replacement λ _ → ∃-and-distributivity) (∃-replacement λ _ → ∃-replacement λ _ → ∃-and-distributivity) ]≡
                       ∃ (λ w' → ∃ λ w'' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i') and ∃ (λ i'' → w'' ∈ x and i'' ∈ y and t == tuple w'' i''))
                       or
                       ∃ (λ w' → ∃ λ w'' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i') and ∃ (λ i'' → w'' ∈ y and i'' ∈ x and t == tuple w'' i''))
                       ≡[ or-replacement ∃-and-distributivity ∃-and-distributivity ]≡
                       ∃ (λ w' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i')) and ∃ (λ w' → ∃ (λ i' → w' ∈ x and i' ∈ y and t == tuple w' i'))
                       or
                       ∃ (λ w' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i')) and ∃ (λ w' → ∃ (λ i' → w' ∈ y and i' ∈ x and t == tuple w' i'))
                       ≡[ ≡-commutativity and-or-distributivity ]≡
                       ∃ (λ w' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i'))
                       and
                       (∃ (λ w' → ∃ (λ i' → w' ∈ x and i' ∈ y and t == tuple w' i')) or ∃ (λ w' → ∃ (λ i' → w' ∈ y and i' ∈ x and t == tuple w' i')))
                       ≡[ ≡-def (and-def and-commutativity and-commutativity) ]≡
                       (∃ (λ w' → ∃ (λ i' → w' ∈ x and i' ∈ y and t == tuple w' i')) or ∃ (λ w' → ∃ (λ i' → w' ∈ y and i' ∈ x and t == tuple w' i')))
                       and
                       ∃ (λ w' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i'))
                       ≡[ ≡-transfer (lm-2 t) ]≡
                       ≡-reflexivity (∃ (λ w' → ∃ (λ i' → w' ∈ z and i' ∈ w and t == tuple w' i')))
          -- lm-4 : (w' i' : 𝕊) → (w' ∈ x and i' ∈ y and t == tuple w' i') or (w' ∈ y and i' ∈ x and t == tuple w' i') ≡ (w' ∈ z and i' ∈ w and t == tuple w' i')
          -- lm-4 = ?
