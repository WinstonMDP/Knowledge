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

_∘_ : {x y z : Set} → (y → z) → (x → y) → (x → z)
_∘_ w i = λ j → w (i j)   
infixl 50 _∘_

postulate
    excluded-middle-ax : (x : Set) → ¬ x or x

postulate
    𝕊 : Set
    _∈_ : 𝕊 → 𝕊 → Set
infix 50 _∈_

data _==_ : 𝕊 → 𝕊 → Set where
    ==-def : {x y : 𝕊} → ((z : 𝕊) → z ∈ x ≡ z ∈ y) → x == y
infixr 50 _==_

postulate
    𝕊-≡-congruence : {x y : 𝕊} → (z : 𝕊 → Set) → x == y → z x ≡ z y
    ==-congruence : {x y : 𝕊} → (z : 𝕊 → 𝕊) → x == y → z x == z y

==-logic-eq : {x y : 𝕊} → x == y → (z : 𝕊) → z ∈ x ≡ z ∈ y
==-logic-eq (==-def x) = x

==-commutativity : {x y : 𝕊} → x == y → y == x
==-commutativity (==-def z) = ==-def λ w → ≡-commutativity (z w)

==-transitivity : {x y z : 𝕊} → x == y → y == z → x == z
==-transitivity (==-def w) (==-def i) = ==-def λ j → ≡-transitivity (w j) (i j)

==-reflexivity : (x : 𝕊) → x == x
==-reflexivity x = ==-def (λ _ → ≡-def (and-def id id))

data _⊆_ : 𝕊 → 𝕊 → Set where
    ⊆-def : {x y : 𝕊} → ((z : 𝕊) → z ∈ x → z ∈ y) → x ⊆ y 
infix 50 _⊆_

⊆-to : {x y : 𝕊} → x ⊆ y → ((z : 𝕊) → z ∈ x → z ∈ y)
⊆-to (⊆-def z) = z

postulate
    eq-ax : {x y : 𝕊} → x == y → (z : 𝕊) → x ∈ z ≡ y ∈ z
    pair-ax : (x y : 𝕊) → ∃ λ z → x ∈ z and y ∈ z and ((w : 𝕊) → w ∈ z ≡ w == x or w == y)
    ∪ : 𝕊 → 𝕊 -- union axiom
    ∪-def : {x y : 𝕊} → (∃ λ z → x ∈ z and z ∈ y) ≡ x ∈ ∪ y
    𝓟 : 𝕊 → 𝕊 -- power axiom
    𝓟-def : {x y : 𝕊} → x ⊆ y ≡ x ∈ (𝓟 y)
    foundation-ax : (x : 𝕊) → ∃ (λ y → y ∈ x) → ∃ λ y → y ∈ x and ((z : 𝕊) → z ∈ x → ¬(z ∈ y))

pair : 𝕊 → 𝕊 → 𝕊
pair x y = ∃-element (pair-ax x y)

pair-∈ : {x y z : 𝕊} → z == x or z == y ≡ z ∈ pair x y 
pair-∈ {x} {y} {z} = ≡-commutativity (and-right (∃-application (pair-ax x y)) z)

pair-left-∈ : {x y : 𝕊} → x ∈ pair x y
pair-left-∈ {x} {y} = (and-left ∘ and-left) (∃-application (pair-ax x y))

pair-right-∈ : {x y : 𝕊} → y ∈ pair x y
pair-right-∈ {x} {y} = (and-right ∘ and-left) (∃-application (pair-ax x y))

pair-==-pair : {x y z w : 𝕊} → x == z and y == w or x == w and y == z ≡ pair x y == pair z w
pair-==-pair {x} {y} {z} {w} = ≡-def (and-def 
                                      (λ {(or-def-left i) → ==-def λ j → ≡-def (and-def
                                                                                (λ k → to
                                                                                       pair-∈
                                                                                       (or-application
                                                                                        (back pair-∈ k)
                                                                                        (λ t → ==-transitivity t (and-left i))
                                                                                         λ t → ==-transitivity t (and-right i)))
                                                                                 λ k → to
                                                                                       pair-∈
                                                                                       (or-application
                                                                                        (back pair-∈ k)
                                                                                        (λ t → ==-transitivity t (==-commutativity (and-left i)))
                                                                                        λ t → ==-transitivity t (==-commutativity (and-right i))));
                                          (or-def-right i) → ==-def λ j → ≡-def (and-def
                                                                                 (λ k → to
                                                                                        pair-∈
                                                                                        (or-commutativity (or-application
                                                                                                           (back pair-∈ k)
                                                                                                           (λ t → ==-transitivity t (and-left i))
                                                                                                           λ t → ==-transitivity t (and-right i))))
                                                                                  λ k → to pair-∈ (or-commutativity (or-application
                                                                                                                     (back pair-∈ k)
                                                                                                                     (λ t → ==-transitivity t (==-commutativity (and-right i)))
                                                                                                                     λ t → ==-transitivity t (==-commutativity (and-left i)))))})
                                      λ {(==-def i) → or-commutativity (or-application
                                                                        (or-application
                                                                         ((to and-or-distributivity) (and-def
                                                                                                      ((back pair-∈) (to (i x) pair-left-∈))
                                                                                                      ((back pair-∈) (to (i y) pair-right-∈))))
                                                                         ((to and-or-distributivity) ∘ and-commutativity)
                                                                         ((to and-or-distributivity) ∘ and-commutativity))
                                                                        (and-commutativity ∘
                                                                         or-absorption ∘
                                                                         or-commutativity ∘
                                                                         (λ j → or-application j (lm-1 ∘ and-def ((back pair-∈) (back (i w) pair-right-∈))) id))
                                                                        (and-commutativity ∘
                                                                         or-absorption ∘
                                                                         (λ j → or-application j id (lm-1 ∘ and-def ((back pair-∈) (back (i z) pair-left-∈))))))})
    where lm-1 : {l m n q : 𝕊} → (l == m or l == n) and (n == q and m == q) → n == q and m == l and l == q
          lm-1 = (λ t → and-def
                        (and-def ((and-left ∘ and-left) t) (==-transitivity ((and-right ∘ and-left) t) ((==-commutativity ∘ and-right) t)))
                        (and-right t)) ∘
                 (to or-idempotency) ∘
                 (λ k → or-application
                        k
                        (λ t → and-def (and-left t) (==-transitivity (and-right t) ((and-right ∘ and-left) t)))
                        λ t → and-def (and-left t) (==-transitivity (and-right t) ((and-left ∘ and-left) t))) ∘
                 (to and-or-distributivity) ∘
                 and-commutativity

singleton : 𝕊 → 𝕊
singleton x = pair x x

singleton-∈ : {x y : 𝕊} → y == x ≡ y ∈ singleton x
singleton-∈ = ≡-def (and-def (λ z → to pair-∈ (or-def-left z)) λ z → to or-idempotency (back pair-∈ z))

singleton-single-∈ : {x : 𝕊} → x ∈ singleton x
singleton-single-∈ {x} = pair-left-∈

singleton-==-singleton : {x y : 𝕊} → x == y ≡ singleton x == singleton y
singleton-==-singleton {x} = ≡-def (and-def
                                    (λ z → ==-congruence singleton z)
                                    λ {(==-def z) → (back singleton-∈) (to (z x) singleton-single-∈)})

singleton-==-pair : {x y z : 𝕊} → x == y and x == z ≡ singleton x == pair y z
singleton-==-pair {_} {y} {z}  = ≡-def (and-def
                                        (λ w → to pair-==-pair (or-def-left w))
                                        λ {(==-def w) → and-def
                                                        (==-commutativity (back singleton-∈ (back (w y) pair-left-∈)))
                                                        (==-commutativity (back singleton-∈ (back (w z) pair-right-∈)))})
    
data 𝕊-∃! : (𝕊 → Set) → Set where
    𝕊-∃!-def : (x : 𝕊 → Set) → (y : 𝕊) → x y → ((z : 𝕊) → x z → y == z) → 𝕊-∃! x

𝕊-∃!-∃ : {x : 𝕊 → Set} → 𝕊-∃! x → ∃ x
𝕊-∃!-∃ (𝕊-∃!-def x y z _) = ∃-def x y z

union : 𝕊 → 𝕊 → 𝕊
union x y = ∪ (pair x y)

union-def : {x y z : 𝕊} → z ∈ x or z ∈ y ≡ z ∈ union x y
union-def {x} {y} {z} = ≡-def (and-def
                         (λ {(or-def-left w) → to
                                               (∪-def {z} {pair x y})
                                               (∃-def (λ i → z ∈ i and i ∈ pair x y) x (and-def w pair-left-∈));
                            (or-def-right w) → to
                                               (∪-def {z} {pair x y})
                                               (∃-def (λ i → z ∈ i and i ∈ pair x y) y (and-def w pair-right-∈))})
                         λ w → lm-2 w (back pair-∈ (and-right (lm-1 w))))
    where lm-1 : (w : z ∈ union x y) → z ∈ ∃-element (back (∪-def {z} {pair x y}) w) and ∃-element (back (∪-def {z} {pair x y}) w) ∈ pair x y
          lm-1 w = ∃-application (back (∪-def {z} {pair x y}) w)
          lm-2 : (w : z ∈ union x y) → ∃-element (back (∪-def {z} {pair x y}) w) == x or ∃-element (back (∪-def {z} {pair x y}) w) == y → z ∈ x or z ∈ y
          lm-2 w i = or-application i ((λ j → to (j z) (and-left (lm-1 w))) ∘ ==-logic-eq) ((λ j → to (j z) (and-left (lm-1 w))) ∘ ==-logic-eq)

postulate
    infinity-ax : ∃ λ x → ((z : 𝕊) → ((w : 𝕊) → ¬(w ∈ z)) → z ∈ x) and ((y : 𝕊) → y ∈ x → (union y (singleton y)) ∈ x)
    substitution-ax : (x : 𝕊 → 𝕊 → Set) → ((y : 𝕊) → 𝕊-∃! (λ z → x y z) or ((z : 𝕊) → ¬(x y z))) → (y : 𝕊) → ∃ λ z → (w : 𝕊) → ∃ (λ j → j ∈ y and x j w) ≡ w ∈ z

subsets-ax : (x : 𝕊) → (y : 𝕊 → Set) → ∃ λ z → (w : 𝕊) → w ∈ x and y w ≡ w ∈ z
subsets-ax x y = lm-3 (∃-application ((lm-1 (λ i → lm-2 i (excluded-middle-ax (y i)))) x))
    where lm-1 = substitution-ax (λ i j → i == j and y i)

          lm-2 : (i : 𝕊) → ¬(y i) or y i → 𝕊-∃! (λ j → i == j and y i) or ((z : 𝕊) → ¬(i == z and y i)) 
          lm-2 i (or-def-left (¬-def k)) = or-def-right λ t → ¬-def λ {(and-def _ q) → k q}
          lm-2 i (or-def-right k) = or-def-left (𝕊-∃!-def (λ j → i == j and y i) i (and-def (==-reflexivity i) k) λ {z (and-def t _) → t})

          lm-3 : ((w : 𝕊) → ∃ (λ j → j ∈ x and (j == w and y j)) ≡ w ∈ ∃-element (lm-1 (λ i → lm-2 i (excluded-middle-ax (y i))) x)) → ∃ λ z → (k : 𝕊) → k ∈ x and y k ≡ k ∈ z
          lm-3 j = ∃-def
                   (λ z → (k : 𝕊) → k ∈ x and y k ≡ k ∈ z)
                   (∃-element (lm-1 (λ i → lm-2 i (excluded-middle-ax (y i))) x))
                   λ t → ≡-def (and-def
                                (λ {(and-def q r) → to (j t) (∃-def (λ j₁ → j₁ ∈ x and (j₁ == t and y j₁)) t (and-def q (and-def (==-reflexivity t) r)))})
                                λ q → and-def
                                      (to (eq-ax ((and-right ∘ and-left) (lm-3-1 t q)) x) ((and-left ∘ and-left) (lm-3-1 t q)))
                                      (to (𝕊-≡-congruence y ((and-right ∘ and-left) (lm-3-1 t q))) (and-right (lm-3-1 t q))))
              where lm-3-1 : (t : 𝕊) →
                             (q : t ∈ ∃-element (lm-1 (λ i → lm-2 i (excluded-middle-ax (y i))) x)) →
                             ∃-element (back (j t) q) ∈ x and ∃-element (back (j t) q) == t and y (∃-element (back (j t) q))
                    lm-3-1 t q = back and-associativity (∃-application (back (j t) q))

∅ : 𝕊
∅ = ∃-element (subsets-ax (∃-element infinity-ax) λ _ → ⊥)

∅-def : (x : 𝕊) → ¬(x ∈ ∅)
∅-def x = ¬-def λ y → and-right (back (∃-application (subsets-ax (∃-element infinity-ax) (λ _ → ⊥)) x) y)

∅-𝕊-∃! : 𝕊-∃! λ x → (y : 𝕊) → ¬(y ∈ x)
∅-𝕊-∃! = 𝕊-∃!-def
         (λ x → (y : 𝕊) → ¬ (y ∈ x))
         ∅
         (λ y → ¬-def λ z → ¬-to-⊥ (∅-def y) z)
         λ y z → ==-def λ w → ≡-def (and-def (λ i → ⊥-to-everything (¬-to-⊥ (∅-def w) i)) λ i → ⊥-to-everything (¬-to-⊥ (z w) i))

x-∈-x-⊥ : (x : 𝕊) → ¬(x ∈ x)
x-∈-x-⊥ x = ¬-def λ y → ¬-to-⊥ (and-right (∃-application (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈))) x singleton-single-∈) (lm-2 y)
    where lm-1 : ∃-element (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈)) == x
          lm-1 = (to or-idempotency) (to
                                      ((and-right (∃-application (pair-ax x x))) (∃-element (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈))))
                                      (and-left (∃-application (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈)))))
          lm-2 : (x ∈ x) → x ∈ ∃-element (foundation-ax (singleton x) (∃-def (λ z → z ∈ singleton x) x singleton-single-∈))
          lm-2 y = back (==-logic-eq lm-1 x) y

set-of-all-sets-⊥ : ¬(∃ λ x → (y : 𝕊) → y ∈ x)
set-of-all-sets-⊥ = ¬-def λ {(∃-def _ z w) → ¬-to-⊥ (x-∈-x-⊥ z) (w z)}

intersection : 𝕊 → 𝕊 → 𝕊
intersection x y = ∃-element (subsets-ax x (λ z → z ∈ y))

intersection-def : (x y z : 𝕊) →  z ∈ x and z ∈ y ≡ z ∈ intersection x y
intersection-def x y z = ∃-application (subsets-ax x (λ z → z ∈ y)) z

tuple : 𝕊 → 𝕊 → 𝕊
tuple x y = pair (singleton x) (pair x y)   

tuple-def : {x y z w : 𝕊} → tuple x y == tuple z w ≡ x == z and y == w
tuple-def {x} {y} {z} {w} = ≡-def (and-def (λ i → lm-1 i) λ i → to pair-==-pair (or-def-left (and-def (to singleton-==-singleton (and-left i)) (to pair-==-pair (or-def-left i)))))
    where lm-1 : tuple x y == tuple z w → x == z and y == w
          lm-1 i = or-absorption (or-application
                                  ((to or-associativity) (or-application
                                                          (back pair-==-pair i)
                                                          ((λ j → or-application
                                                                  j
                                                                  id
                                                                  (back and-associativity)) ∘
                                                           (to and-or-distributivity) ∘
                                                           (λ j → and-application j (back singleton-==-singleton) (back pair-==-pair)))
                                                          ((back and-associativity) ∘
                                                           λ j → and-application
                                                                 j
                                                                 (back singleton-==-pair)
                                                                 (and-commutativity ∘ (λ k → and-application k id ==-commutativity) ∘ (back singleton-==-pair) ∘ ==-commutativity))))
                                  ((λ j → and-application j (to and-idempotency) id) ∘ (back and-associativity))
                                  ((λ j → and-application
                                          j
                                          (λ k → and-application k id (λ _ → ==-transitivity (==-transitivity (and-right j) ((==-commutativity ∘ and-left) k)) (and-right k)))
                                          id) ∘
                                   or-absorption))

_×_ : 𝕊 → 𝕊 → 𝕊
x × y = ∃-element (subsets-ax (𝓟 (𝓟 (union x y))) λ z → ∃ λ w → ∃ λ i → w ∈ x and i ∈ y and z == tuple w i)
infixl 60 _×_

×-def : {x y z : 𝕊} → (∃ λ w → ∃ λ i → w ∈ y and i ∈ z and x == tuple w i) ≡ x ∈ y × z 
×-def {x} {y} {z} = ≡-def (and-def (λ w → to lm-1 (and-def (lm-2 w) w)) λ w → and-right (back lm-1 w))
    where lm-1 = ∃-application (subsets-ax (𝓟 (𝓟 (union y z))) λ w → ∃ λ i → ∃ λ j → i ∈ y and j ∈ z and w == tuple i j) x
          lm-2 : (∃ λ w → ∃ λ i → w ∈ y and i ∈ z and x == (tuple w i)) → x ∈ 𝓟 (𝓟 (union y z))
          lm-2 (∃-def _ w (∃-def _ i j)) = to 𝓟-def (⊆-def λ k t → to 𝓟-def (⊆-def (λ l m → to
                                                                                            union-def
                                                                                            (or-application
                                                                                             (back
                                                                                              or-associativity
                                                                                              (or-application
                                                                                               (back pair-∈ (to ((==-logic-eq ∘ and-right) j k) t))
                                                                                               (λ n → back singleton-∈ (to (==-logic-eq n l) m))
                                                                                               (λ n → back pair-∈ (to (==-logic-eq n l) m))))
                                                                                             ((λ n → back (eq-ax n y) ((and-left ∘ and-left) j)) ∘ to or-idempotency)
                                                                                             (λ n → back (eq-ax n z) ((and-right ∘ and-left) j))))))
    
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
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → (w' ∈ z and i' ∈ w and t == tuple w' i') and (w' ∈ x and i' ∈ y and t == tuple w'' i''))
                       or
                       ∃ (λ w' → ∃ λ w'' → ∃ λ i' → ∃ λ i'' → (w' ∈ z and i' ∈ w and t == tuple w' i') and (w' ∈ y and i' ∈ x and t == tuple w'' i''))
                       ≡[ or-replacement
                          (∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → {!!} ≡[ {!!} ]≡ ≡-reflexivity _)
                          (∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → ∃-replacement λ _ → {!!} ≡[ {!!} ]≡ ≡-reflexivity _)
                       ]≡
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
