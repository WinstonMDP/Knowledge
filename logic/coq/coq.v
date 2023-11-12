Inductive formula (x : Type) : Type :=
  | bot
  | top
  | var (_ : x)
  | neg (_ : formula x)
  | and (_ _ : formula x)
.
Arguments bot {x}.
Arguments top {x}.
Arguments var {x}.
Arguments neg {x}.
Arguments and {x}.

Definition or {x : Type} (y z : formula x) := neg (and (neg y) (neg z)).

Definition estimation (x : Type) := x -> bool.

Fixpoint interpretation {x : Type} (y : estimation x) (z : formula x) : bool :=
  match z with
  | bot => false
  | top => true
  | var w => y w
  | neg w => negb (interpretation y w)
  | and w i => andb (interpretation y w) (interpretation y i)
  end.

Module vec.
Inductive vec (x : Type) : nat -> Type :=
  | nil : vec x 0
  | cons (n : nat) (h : x) (t : vec x n) : vec x (S n)
.
End vec.

Require Vector.

Fixpoint suitable_formula {n : nat} (v : Vector.t bool n) : formula (Fin.t n) :=
  match v with
  | Vector.nil _ => bot
  | Vector.cons _ x n' v' =>
      and
      (suitable_formula v')
      (if x then var (Vector.length n) else neg (var Fin.of_nat n))
  end.

Theorem functional_completeness :
  forall (n : nat) (function : Vector.t bool n -> bool),
  exists (_formula : formula nat),
  forall (v : Vector.t bool n),
    interpretation (Vector.nth v) _formula = function v.
Proof.
  intros.
Qed.
