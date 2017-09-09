Require Import Lists.List.
Require Import ZArith.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.

Open Scope Z_scope.
Import ListNotations.

(**

 Short proof of the inclusion-exclusion principle, which gives the
 cardinality of a finite union of finite sets as an alternating sum of
 cardinalities of the intersections of those sets.

 We choose a formalization of finite sets particularly well suited for
 our purposes: [X] is the universe, or support, of the base sets. We
 suppose the union is finite, and hence we assume a list [enum_X] to
 enumerate all the elements that are in all the considered sets.  In
 fact, we only use [enum_X] to define a constructive [cardinal]
 function, so if enum_X happens to enumerate some elements several
 times, the theorem still holds, which means that it also works if the
 cardinality is "weighted".
 
 Finally, the finiteness of the set of sets is enforced by using a
 list of sets, in which we do not require each set to be unique, so
 the inclusion-exclusion principle also works for a multiset of sets.

*)

Axiom X : Set.
Axiom enum_X : list X.

Definition set := X -> bool.

Definition cardinal (A : set) := Z.of_nat (length (filter A enum_X)).

Definition empty_set : set := fun _ => false.

Definition binary_union (A B : set) x := orb (A x) (B x).

Definition binary_intersection (A B : set) x := andb (A x) (B x).

Infix " ∪ " := binary_union (at level 50).

Infix " ∩ " := binary_intersection (at level 50).

Notation " # " := cardinal.

Lemma cardinal_union_lemma A B : # (A ∪ B) = # A + # B - # (A ∩ B).
Proof.
  cut (# (A ∪ B) + # (A ∩ B) = # A + # B). omega.
  unfold cardinal. repeat rewrite <-Nat2Z.inj_add. f_equal.
  unfold binary_intersection, binary_union in *.
  induction enum_X as [| x l IHl]. reflexivity.
  simpl.
  destruct (A x), (B x); simpl; repeat rewrite <-plus_n_Sm; congruence.
Qed.

Lemma cardinal_binary_union A B :
  cardinal (binary_union A B) =
  cardinal A + cardinal B -
    cardinal (binary_intersection A B).
Proof.
  rewrite <-cardinal_union_lemma. omega.
Qed.

Definition list_union (A : list set) :=
  fold_right binary_union empty_set A.

Definition fold1 {A} (f : A -> A -> A) (l : list A) (default : A) :=
  match l with
  | nil => default
  | x :: xs => fold_right f x xs
  end.

Definition list_intersection (A : list set) :=
  fold1 binary_intersection A empty_set.

Definition set_eq (A B : set) := forall x, A x = B x.

Infix " == " := set_eq (at level 90).

Lemma set_eq_refl : Reflexive set_eq.
Proof.
  compute; congruence.
Qed.

Lemma set_eq_sym : Symmetric set_eq.
Proof.
  compute; congruence.
Qed.

Lemma set_eq_trans : Transitive set_eq.
Proof.
  compute; congruence.
Qed.

Add Parametric Relation : set set_eq
    reflexivity proved by set_eq_refl
    symmetry proved by set_eq_sym
    transitivity proved by set_eq_trans
      as Set_eq.

Instance union_morphism :
  Proper (set_eq ==> set_eq ==> set_eq) binary_union | 10.
Proof.
  intros A B E C D F x. unfold "∪". rewrite E, F. reflexivity.
Qed.

Instance intersection_morphism :
  Proper (set_eq ==> set_eq ==> set_eq) binary_intersection | 10.
Proof.
  intros A B E C D F x. unfold "∩". rewrite E, F. reflexivity.
Qed.

Instance cardinal_morphism :
  Proper (set_eq ==> @eq Z) cardinal | 10.
Proof.
  intros A B E. unfold "#". f_equal. induction enum_X. reflexivity.
  simpl. rewrite E. 
  destruct (B a); simpl; congruence.
Qed.

Lemma cardinal_set_eq (A B : set) : A == B -> # A = # B.
Proof.
  intros E. unfold "#". f_equal.
  induction enum_X as [| a l IHl]; simpl. reflexivity. rewrite E.
  destruct (B a); simpl; congruence.
Qed.

Ltac iftac :=
  let x := fresh "x" in
  intro x; compute;
  repeat
    match goal with
      |- context [ if ?b x then _ else _] => destruct b
    end; try reflexivity.

Ltac Rewrite H :=
  let E := fresh "E" in
  assert (E : H) by iftac; rewrite E; clear E.

Lemma cardinal_ternary_union A B C :
  # (A ∪ B ∪ C) = # A + # B + # C - # (A ∩ B) - #(B ∩ C) - # (C ∩ A) + #(A ∩ B ∩ C).
Proof.
  rewrite cardinal_binary_union.
  Rewrite ((A ∪ B) ∩ C == (A ∩ C) ∪ (B ∩ C)).
  rewrite cardinal_binary_union.
  rewrite cardinal_binary_union.
  Rewrite ((A ∩ C) ∩ (B ∩ C) == (A ∩ B) ∩ C).
  Rewrite (C ∩ A == A ∩ C).
  ring.
Qed.

Fixpoint sublists {A} (xs : list A) : list (list A) :=
  match xs with
  | nil => [[]]
  | x :: xs =>
    let xss := sublists xs in
    xss ++ (map (fun l => x :: l)) xss
  end.

Definition nonempty {A} (xs : list A) :=
  match xs with
    [] => false
  | _ :: _ => true
  end.

Fixpoint sum l :=
  match l with
  | nil => 0
  | x :: l => x + sum l
  end.

Fixpoint alternating_sign n :=
  match n with
  | O => 1
  | S n => - alternating_sign n
  end.

Lemma cardinal_empty : cardinal empty_set = 0.
Proof.
  unfold empty_set, cardinal.
  induction enum_X; auto.
Qed.

Lemma sum_app l1 l2 : sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  induction l1. reflexivity. simpl. omega.
Qed.

Lemma filter_app {A} f (l1 l2 : list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [| a l IHl]; simpl. reflexivity.
  destruct (f a); simpl; congruence.
Qed.

Lemma filter_map_always {A B} f (g : A -> B) l :
  (forall x, f (g x) = true) ->
  filter f (map g l) = map g l.
Proof.
  intros H. induction l as [| a l IHl]. reflexivity. simpl.
  rewrite H. congruence.
Qed.

Lemma sublists_proper {A} (l : list A) :
  sublists l = [] :: filter nonempty (sublists l).
Proof.
  induction l as [| a l IHl]. reflexivity. simpl.
  rewrite IHl at 1. simpl. rewrite filter_app.
  rewrite filter_map_always; reflexivity.
Qed.

Lemma sublists_map {A B} (f : A -> B) l :
  sublists (map f l) = map (map f) (sublists l).
Proof.
  induction l as [| a l IHl]. reflexivity. simpl.
  rewrite map_app, IHl. f_equal. clear.
  induction (sublists l) as [| x xs IHxs]. reflexivity.
  simpl. f_equal. auto.
Qed.

Theorem inclusion_exclusion (l : list set) :
  cardinal (list_union l) =
  sum
    (map (fun l' => cardinal (list_intersection l') *
                 alternating_sign (1 + length l'))
         (filter nonempty (sublists l))).
Proof.
  match goal with |- context [ map ?F ] => set (f := F) end.
  remember (length l) as n. revert l Heqn.
  induction n; intros l En.
  destruct l; [ | discriminate].
  unfold list_union, f. simpl. rewrite cardinal_empty. reflexivity.
  destruct l as [| a l]; [ discriminate | ].
  simpl in En. injection En as En.
  simpl.
  rewrite cardinal_binary_union.
  rewrite filter_app, map_app, sum_app.
  rewrite IHn; auto.
  pose (la := map (fun b => a ∩ b) l).
  replace (# (a ∩ list_union l)) with (# (list_union la)); swap 1 2.
  { apply cardinal_set_eq. unfold la; clear. induction l. simpl. iftac.
    simpl.
    rewrite IHl. iftac. }
  rewrite IHn; swap 1 2.
  { unfold la. rewrite map_length. auto. }
  
  match goal with |- ?a + ?b - ?c = ?b + ?d => cut (a - c = d) end.
  { intros <-. ring. }
  
  unfold la. clear la n En IHn.
  rewrite filter_map_always; auto.
  rewrite (sublists_proper l). simpl.
  unfold f at 2. simpl. ring_simplify. unfold Z.sub. f_equal.
  rewrite sublists_map.
  generalize (sublists l); clear l; intros l.
  
  replace (filter nonempty (map (map (fun b : set => a ∩ b)) l))
  with (map (map (fun b : set => a ∩ b)) (filter nonempty l)); swap 1 2.
  {
    induction l as [| b l IHl]. reflexivity. simpl.
    destruct b; simpl; congruence.
  }
  induction l as [| b l IHl]. reflexivity.
  simpl.
  destruct b as [| x xs]. simpl. congruence.
  simpl. rewrite <-IHl. ring_simplify.
  match goal with |- - ?x - ?b = - ?b + ?y => cut (x = - y) end.
  { intros ->. ring. }
  unfold f. clear IHl l f.
  
  simpl (alternating_sign _). rewrite map_length. ring_simplify.
  match goal with |- ?x * ?b = ?b * ?y => cut (x = y) end.
  { intros ->. ring. }
  
  simpl. apply cardinal_set_eq.
  induction xs as [ | x' xs IHxs ]. simpl. iftac.
  simpl. rewrite IHxs.
  cut (fold_right binary_intersection a xs == a ∩ fold_right binary_intersection a xs).
  { intros ->. iftac. }
  clear.
  induction xs. simpl. iftac.
  simpl. rewrite IHxs. iftac.
Qed.
