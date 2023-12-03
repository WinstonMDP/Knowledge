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

Require List.

Fixpoint nth {x : Type} (v : Vector.t x size) (index : nat) (H : index < size) : x.
Proof.
  destruct v as [| vh size' vt] eqn:E.
  - exfalso. apply (PeanoNat.Nat.nlt_0_r index). apply H.
  - unfold lt in H.
    destruct index as [| index'].
    + apply vh.
    + apply nth with size' index'.
      * apply vt.
      * unfold lt. apply le_S_n. apply H.
Defined.

Fixpoint suitable_formula {n : nat} (l : List.list bool) (acc : nat) : formula nat :=
  match l with
  | [] => top
  | x :: y => and (suitable_formula y (S acc)) (if x then var acc else neg (var acc))
  end.

Theorem suitable_formula_true :
  forall n (v : Vector.t bool n) f,
  f v = true ->
  interpretation
  (fun i => List.nth i (Vector.to_list v) false)
  (suitable_formula v) =
  true.
Proof.
  intros n v f H.
  induction v as [| vh n' vt IH].
  - reflexivity.
  - unfold suitable_formula.
    fold (suitable_formula vt).
    specialize (IH (fun _ => true)).
    simpl in IH.
    specialize (IH (eq_refl true)).
    assert (H' :
      forall (x y : formula nat) e,
        interpretation e (and x y) = andb (interpretation e x) (interpretation e y)
    ).
    { reflexivity. }
    rewrite H'.
Admitted.

Fixpoint bool_force (n : nat) : list (Vector.t bool n) :=
  match n with
  | O => List.cons Vector.nil List.nil
  | S n' =>
      List.map (Vector.cons false n') (bool_force n') ++
      List.map (Vector.cons true n') (bool_force n')
  end.

Theorem all_in_force : forall {n : nat} (v : Vector.t bool n), List.In v (bool_force n).
Proof.
Admitted.

Definition suitable_formulas_formula {n : nat} (f : Vector.t bool n -> bool) : formula nat :=
  List.fold_right or bot (List.map suitable_formula (List.filter f (bool_force n))).

Theorem or_introduce_left :
  forall (t : Type) (x : formula t) y e,
    interpretation e x = true -> interpretation e (or x y) = true.
Proof. intros t x y e H. unfold or. simpl. rewrite H. reflexivity. Qed.

Theorem or_introduce_right :
  forall (t : Type) (x : formula t) y e,
    interpretation e y = true -> interpretation e (or x y) = true.
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
    List.In f fs -> interpretation e f = true ->
      interpretation e (List.fold_right or bot fs) = true.
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

Theorem functional_completeness :
  forall (n : nat) (function : (forall l : list bool) -> (length l = n) -> bool),
  exists (form : formula nat),
  forall (l : list bool),
  (length l = n) -> interpretation (fun i => List.nth i l false) form = function v.
Proof.
  intros n function.
  exists (suitable_formulas_formula function).
  intros v.
  destruct (function v) eqn:E.
  - unfold suitable_formulas_formula.
    set (conj (all_in_force v) E) as H.
    rewrite <- List.filter_In in H.
    apply (List.in_map suitable_formula) in H.
    apply or_fold_in with (suitable_formula v).
    + apply H.
    + apply suitable_formula_true with function. apply E.
  - unfold suitable_formulas_formula.
    set (conj (all_in_force v) E) as H.
    apply proj1 in H.
    "list"
    rewrite <- List.filter_In in H.
    apply (List.in_map suitable_formula) in H.
    apply or_fold_in with (suitable_formula v).

  induction v as [| vh n' vt IH].
  - cbn.
    destruct (function Vector.nil) eqn:E.
    + reflexivity.
    + reflexivity.
  - simpl.
    destruct (Vector.cons vh n' vt) .
Qed.
