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

union-⊆ : {x y : 𝕊} → x ⊆ y ≡ union x y == y
union-⊆ {x} {y} = ≡-def (and-def
                         (λ {(⊆-def z) → ==-def λ w → ≡-def (and-def
                                                             (λ i → to or-idempotency (or-application (back (union-def {x} {y} {w}) i) (z w) id))
                                                             λ i → to (union-def {x} {y} {w}) (or-def-right i))})
                         λ {(==-def j) → ⊆-def λ w i → to (j w) (to (union-def {x} {y} {w}) (or-def-left i))})

==-double-⊆ : {x y : 𝕊} → x ⊆ y and y ⊆ x ≡ x == y
==-double-⊆ = ≡-def (and-def
                     (λ z → ==-def (λ w → ≡-def (and-def (⊆-to (and-left z) w) (⊆-to (and-right z) w))))
                     λ w → and-def (⊆-def (λ i → to (==-logic-eq w i))) (⊆-def (λ i → back (==-logic-eq w i))))

×-== : {x y z w : 𝕊} → x == z and y == w ≡ x × y == z × w
×-== = {!!}

union-commutativity : {x y : 𝕊} → union x y == union y x
union-commutativity = {!!}

square : 𝕊 → 𝕊
square x = x × x

==-2-congruence : {x y z w : 𝕊} → (i : 𝕊 → 𝕊 → 𝕊) → x == z → y == w → i x y == i z w
==-2-congruence = {!!}
     
th-5 : (x y z w : 𝕊) → ¬(x == ∅) → ¬(y == ∅) → union (x × y) (y × x) == z × w → x == y and y == z and z == w
th-5 x y z w i j k = and-def (and-def {!!} {!!}) lm-11
    where lm-2 = λ t → ≡-transitivity (or-replacement (×-def {t} {x} {y}) (×-def {t} {y} {x})) (≡-transitivity (≡-transitivity union-def (==-logic-eq k t)) (≡-commutativity ×-def))
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
          lm-5 : (w' i' t : 𝕊) → (w' ∈ x and i' ∈ y and t == tuple w' i') or (w' ∈ y and i' ∈ x and t == tuple w' i') ≡ (w' ∈ z and i' ∈ w and t == tuple w' i')
          lm-5 w' i' = {!!}
          lm-8 : {t : 𝕊} → ¬(t == ∅) → ∃ λ l → l ∈ t
          lm-8 {t} l = ∃-def (λ m → m ∈ t) {!!} {!!}
          lm-9 : ¬(z == ∅) and ¬(w == ∅)
          lm-9 = {!!}
          lm-1 : union x y == z
          lm-1 = ==-def λ t → ≡-def (and-def
                                     (λ l → to
                                            or-idempotency
                                            (or-application
                                             (back union-def l)
                                             (λ m → (and-left ∘ and-left) (to
                                                                           (lm-5 t (∃-element (lm-8 j)) (tuple t (∃-element (lm-8 j))))
                                                                           (or-def-left (and-def (and-def m (∃-application (lm-8 j))) (==-reflexivity _)))))
                                             (λ m → (and-left ∘ and-left) (to
                                                                           (lm-5 t (∃-element (lm-8 i)) (tuple t (∃-element (lm-8 i))))
                                                                           (or-def-right (and-def (and-def m (∃-application (lm-8 i))) (==-reflexivity _)))))))
                                     (λ l → to
                                            union-def
                                            (or-application
                                             (back
                                              (lm-5 t (∃-element (lm-8 (and-right lm-9))) (tuple t (∃-element (lm-8 (and-right lm-9)))))
                                              (and-def (and-def l (∃-application (lm-8 (and-right lm-9)))) (==-reflexivity _)))
                                             (and-left ∘ and-left)
                                             (and-left ∘ and-left))))
          lm-10 : union y x == w
          lm-10 = ==-def λ t → ≡-def (and-def (λ l → to
                                                     or-idempotency
                                                     (or-application
                                                      (back union-def l)
                                                      (λ m → (and-right ∘ and-left) (to
                                                                                     (lm-5 (∃-element (lm-8 i)) t (tuple (∃-element (lm-8 i)) t))
                                                                                     (or-def-left (and-def (and-def (∃-application (lm-8 i)) m) (==-reflexivity _)))))
                                                      λ m → (and-right ∘ and-left) (to
                                                                                    (lm-5 (∃-element (lm-8 j)) t (tuple (∃-element (lm-8 j)) t))
                                                                                    (or-def-right (and-def (and-def (∃-application (lm-8 j)) m) (==-reflexivity _))))))
                                              (λ l → to
                                                     union-def
                                                     (or-application
                                                      (back
                                                       (lm-5 (∃-element (lm-8 (and-left lm-9))) t (tuple (∃-element (lm-8 (and-left lm-9))) t))
                                                       (and-def (and-def (∃-application (lm-8 (and-left lm-9))) l) (==-reflexivity _)))
                                                      (and-right ∘ and-left)
                                                      (and-right ∘ and-left))))
          lm-11 : z == w
          lm-11 = ==-transitivity (==-commutativity lm-1) (==-transitivity union-commutativity lm-10)
          lm-14 : square (union x y) == union (union (square x) (square y)) (union (x × y) (y × x))
          lm-14 = {!!}
          lm-13 : union (square x) (square y) ⊆ union (x × y) (y × x)
          lm-13 = back
                  union-⊆
                  (==-transitivity (==-commutativity lm-14) (==-transitivity (==-2-congruence _×_ lm-1 lm-1) (==-transitivity (==-congruence (λ i → z × i) lm-11) (==-commutativity k))))
          lm-12 : x == y
          lm-12 = to ==-double-⊆ (and-def {!!} {!!})
