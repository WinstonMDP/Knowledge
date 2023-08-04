module logic where

open Agda.Primitive using (Level)

id : {x : Level} → {y : Set x} → y → y
id z = z

data _and_ : Set → Set → Set where
    and-def : {x y : Set} → x → y → x and y
infixl 40 _and_

and-left : {x y : Set} → x and y → x
and-left (and-def z _) = z

and-right : {x y : Set} → x and y → y
and-right (and-def _ z) = z

and-application : {x y z w : Set} → (x and y) → (x → z) → (y → w) → (z and w)
and-application {_} {_} {z} {w} (and-def i j) k t = and-def {z} {w} (k i) (t j)

and-commutativity : {x y : Set} → x and y → y and x
and-commutativity (and-def z w) = and-def w z

data _≡_ : Set → Set → Set where
    ≡-def : {x y : Set} → (x → y) and (y → x) → x ≡ y
infixr 30 _≡_

to : {x y : Set} → x ≡ y → x → y
to (≡-def (and-def z _)) = z

back : {x y : Set} → x ≡ y → y → x
back (≡-def (and-def _ z)) = z

≡-reflexivity : (x : Set) → x ≡ x
≡-reflexivity x = ≡-def (and-def id id)

≡-commutativity : {x y : Set} → x ≡ y → y ≡ x
≡-commutativity (≡-def (and-def z w)) = ≡-def (and-def w z)

≡-transitivity : {x y z : Set} → x ≡ y → y ≡ z → x ≡ z
≡-transitivity (≡-def (and-def i j)) (≡-def (and-def k t)) = ≡-def (and-def (λ l → k (i l)) λ l → j (t l))

postulate
    ≡-congruence : {x y : Set} → (z : Set → Set) → x ≡ y → z x ≡ z y

≡-congruence-2 : (x y z w : Set) → (i : Set → Set → Set) → x ≡ z → y ≡ w → i x y ≡ i z w
≡-congruence-2 x y z w i j k = ≡-transitivity (lm-2 y) (lm-1 z)
    where lm-1 = λ t → ≡-congruence (i t) k
          lm-2 = λ t → ≡-congruence (λ l → (i l t)) j

≡-transfer : {x y : Set} → x ≡ y → x and y ≡ y
≡-transfer z = ≡-def (and-def (λ w → to z (and-left w)) (λ w → and-def (back z w) w))

_≡[_]≡_ : (x : Set) → {y z : Set} → x ≡ y → y ≡ z → x ≡ z
_≡[_]≡_ x w i = ≡-transitivity w i 
infixr 10 _≡[_]≡_

and-idempotency : {x : Set} → x and x ≡ x
and-idempotency = ≡-def (and-def (λ {(and-def y _) → y}) λ y → and-def y y)

and-associativity : {x y z : Set} → (x and y) and z ≡ x and (y and z)
and-associativity = ≡-def (and-def (λ {(and-def (and-def w i) j) → and-def w (and-def i j)}) λ {(and-def w (and-def i j)) → and-def (and-def w i) j})
 
data ∃ : {x : Set} → (x → Set) → Set where
    ∃-def : {x : Set} → (y : x → Set) → (z : x) → y z → ∃ y

∃-element : {x : Set} → {y : x → Set} → ∃ y → x
∃-element (∃-def _ z _) = z

∃-application : {x : Set} → {y : x → Set} → (z : ∃ y) → y (∃-element z)
∃-application (∃-def _ _ w) = w

∃-replacement : {x : Set} → {y z : x → Set} → ((w : x) → y w ≡ z w) → ∃ y ≡ ∃ z
∃-replacement {_} {y} {z} w = ≡-def (and-def (λ {(∃-def _ i j) → ∃-def z i (to (w i) j)}) λ {(∃-def _ i j) → ∃-def y i (back (w i) j)})

∃-and-distributivity : {x : Set} → {y z : x → Set} → ∃ (λ i → ∃ λ j → y i and z j) ≡ ∃ y and ∃ z
∃-and-distributivity {_} {y} {z} = ≡-def (and-def
                                          (λ {(∃-def _ w (∃-def _ i j)) → and-def (∃-def y w (and-left j)) (∃-def z i (and-right j))})
                                          λ {(and-def w i) → ∃-def _ (∃-element w) (∃-def _ (∃-element i) (and-def (∃-application w) (∃-application i)))})

data ⊥ : Set where

⊥-to-everything : {x : Set} → ⊥ → x
⊥-to-everything ()

data ¬ : Set → Set where
    ¬-def : {x : Set} → (x → ⊥) → ¬ x

¬-to-⊥ : {x : Set} → ¬ x → x → ⊥
¬-to-⊥ (¬-def y) = y

data _or_ : Set → Set → Set where
    or-def-left : {x y : Set} → x → x or y
    or-def-right : {x y : Set} → y → x or y
infixl 35 _or_

or-application : {x y z w : Set} → x or y → (x → z) → (y → w) → z or w
or-application {_} {_} {z} {w} (or-def-left i) j _ = or-def-left {z} {w} (j i)
or-application {_} {_} {z} {w} (or-def-right i) _ j = or-def-right {z} {w} (j i)

or-replacement : {x y z w : Set} → x ≡ z → y ≡ w → x or y ≡ z or w
or-replacement {x} {y} {z} {w} i j = ≡-def (and-def
                                            (λ {(or-def-left k) → or-def-left (to i k); (or-def-right k) → or-def-right (to j k)})
                                            λ {(or-def-left k) → or-def-left (back i k); (or-def-right k) → or-def-right (back j k)})

or-commutativity : {x y : Set} → x or y → y or x
or-commutativity (or-def-left z) = or-def-right z
or-commutativity (or-def-right z) = or-def-left z

or-associativity : {x y z : Set} → (x or y) or z ≡ x or (y or z)
or-associativity = ≡-def (and-def
                          (λ {(or-def-left (or-def-left w)) → or-def-left w;
                              (or-def-left (or-def-right w)) → or-def-right (or-def-left w);
                              (or-def-right w) → or-def-right (or-def-right w)})
                          λ {(or-def-left w) → or-def-left (or-def-left w);
                             (or-def-right (or-def-left w)) → or-def-left (or-def-right w);
                             (or-def-right (or-def-right w)) → or-def-right w})

or-idempotency : {x : Set} → x or x ≡ x
or-idempotency {x} = ≡-def (and-def (λ {(or-def-left y) → y; (or-def-right y) → y}) λ y → or-def-left y)

or-absorption : {x y : Set} → x or x and y → x
or-absorption (or-def-left z) = z
or-absorption (or-def-right (and-def z _)) = z

or-and-distributivity : {x y z : Set} → x or y and z ≡ (x or y) and (x or z)
or-and-distributivity = ≡-def (and-def
                               (λ {(or-def-left w) → and-def (or-def-left w) (or-def-left w); (or-def-right w) → and-def (or-def-right (and-left w)) (or-def-right (and-right w))})
                               (λ {(and-def (or-def-left w) i) → or-def-left w;
                                   (and-def (or-def-right w) (or-def-left i)) → or-def-left i;
                                   (and-def (or-def-right w) (or-def-right i)) → or-def-right (and-def w i)}))

and-or-distributivity : {x y z : Set} → x and (y or z) ≡ x and y or x and z
and-or-distributivity = ≡-def (and-def (λ {(and-def w (or-def-left i)) → or-def-left (and-def w i); (and-def w (or-def-right i)) → or-def-right (and-def w i)})
                                       (λ {(or-def-left w) → and-def (and-left w) (or-def-left (and-right w)); (or-def-right w) → and-def (and-left w) (or-def-right (and-right w))}))

-- ∃-or-distributivity : {x : Set} → {y z : x → Set} → ∃ (λ i → ∃ λ j → y i or z j) ≡ ∃ y or ∃ z
-- ∃-or-distributivity = {!!}

_∘_ : {x y z : Set} → (y → z) → (x → y) → (x → z)
_∘_ w i = λ j → w (i j)
infixl 50 _∘_

postulate
    excluded-middle-ax : (x : Set) → ¬ x or x
