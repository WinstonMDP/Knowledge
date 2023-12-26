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

Fixpoint interpretation {x : Type} (z : formula x) (y : estimation x) : bool :=
  match z with
  | bot => false
  | top => true
  | var w => y w
  | neg w => negb (interpretation w y)
  | and w i => andb (interpretation w y) (interpretation i y)
  end.

Require Import List.
Import List.ListNotations.

Theorem or_bot : forall (T : Type) (f : formula T) e,
  interpretation (or bot f) e = interpretation f e.
Proof. intros. simpl. rewrite Bool.negb_involutive. reflexivity. Qed.

Theorem or_introduce_left :
  forall (t : Type) (x : formula t) y e,
  interpretation x e = true -> interpretation (or x y) e = true.
Proof. intros t x y e H. unfold or. simpl. rewrite H. reflexivity. Qed.

Theorem or_introduce_right :
  forall (t : Type) (x : formula t) y e,
  interpretation y e = true -> interpretation (or x y) e = true.
Proof.
  intros t x y e H.
  unfold or.
  simpl.
  rewrite H.
  simpl.
  rewrite Bool.andb_false_r.
  reflexivity.
Qed.

Theorem or_fold_in :
  forall (x : Type) (f : formula x) fs e,
  In f fs -> interpretation f e = true ->
  interpretation (fold_right or bot fs) e = true.
Proof.
  intros x f.
  induction fs as [| fsh fst IH].
  - contradiction.
  - simpl.
    intros e [H1 | H1] H2.
    + rewrite H1. rewrite H2. reflexivity.
    + simpl.
      set (IH e H1 H2) as H3.
      rewrite H3.
      simpl.
      rewrite Bool.andb_false_r.
      reflexivity.
Qed.

Fixpoint suitable_formula' (l : list bool) (acc : nat) : formula nat :=
  match l with
  | [] => top
  | x :: y => and (if x then var acc else neg (var acc)) (suitable_formula' y (S acc))
  end.

Theorem suitable_formula_next :
  forall (l : list bool) b,
  interpretation (suitable_formula' l 0) (fun i => nth i l false) =
  interpretation (suitable_formula' l 1) (fun i => match i with
                                                   | 0 => b
                                                   | S i => nth i l false
                                                   end).
Proof.
  induction l as [| lh lt IH].
  - reflexivity.
  - simpl in *.
    intros.
    destruct lh eqn:E.
    + simpl in *.
      rewrite <- IH.
Admitted.

Definition suitable_formula (l : list bool) : formula nat := suitable_formula' l 0.

Theorem suitable_formula_true :
  forall (l : list bool),
  interpretation (suitable_formula l) (fun i => nth i l false) = true.
Proof.
  induction l as [| lh lt IH].
  - reflexivity.
  - simpl.
    rewrite Bool.andb_true_iff.
    split.
    + destruct lh.
      * reflexivity.
      * reflexivity.
    + rewrite <- suitable_formula_next.
      apply IH.
Qed.

Fixpoint bool_force (n : nat) : list (list bool) :=
  match n with
  | O => [[]]
  | S n' => map (cons false) (bool_force n') ++ map (cons true) (bool_force n')
  end.

Theorem all_in_force : forall (l : list bool), In l (bool_force (length l)).
Proof.
  intros.
  induction l as [| lh lt IH].
  - simpl. left. reflexivity.
  - simpl.
    apply in_or_app.
    destruct lh.
    + right. apply in_map. apply IH.
    + left. apply in_map. apply IH.
Qed.

Definition suitable_formulas_formula (n : nat) (f : list bool -> bool) : formula nat :=
  fold_right or bot (map suitable_formula (filter f (bool_force n))).


Theorem functional_completeness :
  forall (n : nat) (fn : list bool -> bool),
  exists (form : formula nat),
  forall (l : list bool),
  length l = n -> interpretation form (fun i => nth i l false) = fn l.
Proof.
  intros n fn.
  exists (suitable_formulas_formula n fn).
  intros l H1.
  unfold suitable_formulas_formula.
  destruct (fn l) eqn:E.
  - set (conj (all_in_force l) E) as H2.
    rewrite <- filter_In in H2.
    apply (in_map suitable_formula) in H2.
    apply or_fold_in with (suitable_formula l).
    + rewrite <- H1. apply H2.
    + apply suitable_formula_true.
  - unfold suitable_formulas_formula.
    set (conj (all_in_force l) E) as H.
    apply proj1 in H.
Admitted.
