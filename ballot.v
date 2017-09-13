Require Import Arith.
Require Import ZArith.
Require Import String.
Require Import List.
Require Import Psatz.
Require Import Factorial.

(* Reccurence part of the inductive proof:  *)

Lemma recurrence a b Afirst Bfirst all Afirst_ahead Bfirst_ahead ahead :
  0 < b -> b < a ->
  (a + b) * Afirst = a * all ->
  (a + b) * Bfirst = b * all ->
  Afirst + Bfirst = all ->
  (a - 1 + b) * Afirst_ahead = (a - b - 1) * Afirst ->
  (a - 1 + b) * Bfirst_ahead = (a - (b - 1)) * Bfirst ->
  Afirst_ahead + Bfirst_ahead = ahead ->
  (a + b) * ahead = (a - b) * all.
Proof.
  destruct a. intros ? ?; exfalso; omega.
  destruct b. inversion 1.
  simpl (S a - 1).
  simpl (S b - 1).
  replace (S a - S b - 1) with (a - S b) by omega.
  replace (b - 0) with b by omega.
  replace (a - 0) with a by omega.
  intros _ L HA HB <- IHA IHB <-.
  apply Nat.mul_cancel_l with (p := (a + S b)). omega.
  match goal with |- ?x * (?y * ?z) = _ => transitivity (y * (x * z)) end. ring.
  rewrite Nat.mul_add_distr_l. rewrite IHA, IHB.
  rewrite Nat.mul_add_distr_l.
  match goal with
    |- ?x * (?y * ?z) + ?x' * (?y' * ?z') = _ =>
    transitivity (y * (x * z) + y' * (x' * z'))
  end. ring.
  rewrite HA, HB.
  match goal with
    |- ?x * (?y * ?z) + ?x' * (?y' * ?z) = _ =>
    transitivity ((x * y + x' * y') * z)
  end. ring.
  rewrite mult_assoc.
  f_equal.
  nia.
Qed.

Import ListNotations.

Fixpoint cartesian_product {A B} (xs : list A) (ys : list B) : list (A * B) :=
  match xs with
  | [] => []
  | x :: xs => map (pair x) ys ++ cartesian_product xs ys
  end.

Fixpoint picks {A} n (l : list A) : list (list A) :=
  match n with
  | O => [[]]
  | S n => map (fun x => fst x :: snd x) (cartesian_product l (picks n l))
  end.

Fixpoint pickbools n :=
  match n with
  | O => [[]]
  | S n => map (cons true) (pickbools n) ++ map (cons false) (pickbools n)
  end.

(** non empty suffixes *)
Fixpoint proper_suffixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: l => (x :: l) :: proper_suffixes l
  end.

(** For our notion of "throughout" we choose that lists represent the
    last vote first, and hence we use suffixes *)
Definition throughout {A} f (l : list A) := forallb f (proper_suffixes l).

Definition countb b l := count_occ Bool.bool_dec l b.

Notation length := length.

Lemma countb_false l : countb false l = length l - countb true l.
Proof.
  cut (countb false l + countb true l = length l). omega.
  induction l as [| [|] l IHl]; simpl; omega.
Qed.

Definition winb votes := countb false votes <? countb true votes.

Definition sumtrue p l := countb true l =? p.

Lemma filter_app {A} f (l1 l2 : list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [| a l IHl]; simpl. reflexivity.
  destruct (f a); simpl; congruence.
Qed.

Lemma map_filter {A B} f (g : A -> B) l :
  filter f (map g l) = map g (filter (fun b => f (g b)) l).
Proof.
  induction l; auto. simpl.
  destruct (f (g a)); auto.
  simpl. congruence.
Qed.

Lemma filter_filter {A} (f g : A -> bool) l :
  filter f (filter g l) = filter (fun b => andb (g b) (f b)) l.
Proof.
  induction l; auto. simpl. unfold andb.
  destruct (g a); simpl; destruct (f a); simpl; auto.
  rewrite IHl. auto.
Qed.

Lemma filter_ext {A} f g l : (forall x : A, f x = g x) -> filter f l = filter g l.
Proof.
  intros E.
  induction l; simpl; auto. rewrite E, IHl. auto.
Qed.

Lemma filter_sub {A} f g l : (forall x : A, f x = true -> g x = true) -> filter f l = filter g (filter f l).
Proof.
  intros H.
  induction l; simpl; auto. rewrite IHl. destruct (f a) eqn:E.
  - simpl. rewrite H; auto. congruence.
  - congruence.
Qed.

Fixpoint binomial (n k : nat) : nat :=
  match n with
  | 0 =>
    match k with
    | 0 => 1
    | S _ => 0
    end
  | S n' =>
    match k with
    | 0 => 1
    | S k' => (binomial n' k') + (binomial n' k)
    end
  end.

Lemma binomial_lt n p : n < p -> binomial n p = 0.
Proof.
  revert p.
  induction n; intros [ | p ] H.
  - omega.
  - reflexivity.
  - omega.
  - simpl. rewrite IHn. 2:omega. rewrite IHn; omega.
Qed.

Lemma binomial_0_r n : binomial n 0 = 1.
Proof.
  destruct n; reflexivity.
Qed.

Lemma binomial_1_r n : binomial n 1 = n.
Proof.
  induction n. reflexivity. simpl. rewrite binomial_0_r. omega.
Qed.

Lemma binomial_diag n : binomial n n = 1.
Proof.
  induction n. reflexivity.
  simpl. rewrite IHn. rewrite binomial_lt; omega.
Qed.

Lemma binomial_factorial n k : k <= n -> fact k * fact (n - k) * binomial n k = fact n.
Proof.
  revert k; induction n; intros [ | k].
  - reflexivity.
  - omega.
  - intros _. simpl. omega.
  - intros L. simpl (binomial _ _).
    rewrite Nat.mul_add_distr_l.
    replace (fact (S k) * fact (S n - S k) * binomial n k)
    with ((S k) * (fact k * fact (n - k) * binomial n k))
      by (simpl; ring).
    rewrite IHn. 2:omega.
    assert (D : k = n \/ k < n) by omega. destruct D as [D | D].
    + subst k. rewrite binomial_lt; auto. simpl; ring.
    + replace (S n - S k) with (S (n - S k)) by omega.
      replace (fact (S k) * fact (S (n - S k)) * binomial n (S k))
      with (S (n - S k) * (fact (S k) * fact (n - S k) * binomial n (S k)))
        by (simpl; ring).
      rewrite IHn. 2:omega.
      rewrite <-Nat.mul_add_distr_r.
      change (fact (S n)) with (S n * fact n).
      apply Nat.mul_cancel_r. apply fact_neq_0.
      omega.
Qed.

Lemma binomial_complement n k : k <= n -> binomial n k = binomial n (n - k).
Proof.
  intros L.
  pose (x := fact k * fact (n - k)).
  cut (x * binomial n k = x * binomial n (n - k)).
  { apply Nat.mul_cancel_l. subst x. apply Nat.neq_mul_0; split; apply fact_neq_0. }
  subst x.
  rewrite binomial_factorial; auto.
  rewrite <-(binomial_factorial n (n - k)). 2:omega.
  replace (n - (n - k)) with k by omega.
  ring.
Qed.

Lemma binomial_S n k :
  k <= n ->
  S n * binomial n k = S k * binomial (S n) (S k).
Proof.
  intros Hkn.
  pose (x := fact k * fact (n - k)).
  pose (y := fact (S k) * fact (S n - S k)).
  cut (x * y * (S n * binomial n k) = x * y * (S k * binomial (S n) (S k))).
  { apply Nat.mul_cancel_l. subst x y. do 2 (apply Nat.neq_mul_0; split); apply fact_neq_0. }
  subst x y.
  cut ((fact (S k) * fact (S n - S k)) * (S n * (fact k * fact (n - k) *  binomial n k)) =
       fact k * fact (n - k) * (S k * ((fact (S k) * fact (S n - S k)) * binomial (S n) (S k)))).
  { intros E. etransitivity; [ | etransitivity ]; [ | apply E | ]; ring. }
  rewrite binomial_factorial.
  rewrite binomial_factorial.
  simpl; ring.
  omega.
  auto.
Qed.

Lemma count_sumtrue_cons_true p l :
  filter (sumtrue (S p)) (map (cons true) l) =
  map (cons true) (filter (sumtrue p) l).
Proof.  
  induction l; auto. simpl.
  change (sumtrue (S p) (true :: a)) with (sumtrue p a).
  destruct (sumtrue p a); auto.
  simpl. congruence.
Qed.

Lemma count_0_wins_cons_true l :
  filter (sumtrue 0) (map (cons true) l) = [].
Proof.
  induction l; auto.
Qed.

Lemma count_sumtrue_cons_false p l :
  filter (sumtrue p) (map (cons false) l) =
  map (cons false) (filter (sumtrue p) l).
Proof.
  induction l; auto. simpl.
  change (sumtrue p (false :: a)) with (sumtrue p a).
  destruct (sumtrue p a); auto.
  simpl. congruence.
Qed.

Lemma count_sumtrue p n :
  length (filter (sumtrue p) (pickbools n)) = binomial n p.
Proof.
  revert p.
  induction n; intros p. simpl. destruct p; reflexivity.
  simpl (pickbools _).
  rewrite filter_app, app_length.
  destruct p.
  - replace (binomial (S n) 0) with (0 + binomial (S n) 0) by auto; f_equal.
    + clear. induction (pickbools n); auto.
    + rewrite count_sumtrue_cons_false, map_length.
      rewrite IHn.
      destruct n; auto.
  - simpl.
    f_equal; rewrite <-IHn.
    all: rewrite map_filter, map_length; reflexivity.
Qed.

Lemma first_vote_split p q :
  filter (sumtrue (1 + p)) (pickbools (1 + p + q)) =
  map (cons true) (filter (sumtrue p) (pickbools (p + q))) ++
  map (cons false) (filter (sumtrue (1 + p)) (pickbools (p + q))).
Proof.
  (* true but easy *)
  simpl (pickbools _).
  rewrite filter_app.
  rewrite map_filter.
  rewrite map_filter.
  reflexivity.
Qed.

Lemma pickbools_length n : pickbools n = filter (fun l => length l =? n) (pickbools n).
Proof.
  induction n. reflexivity.
  simpl. rewrite filter_app.
  do 2 rewrite map_filter. f_equal; f_equal; f_equal.
  all: etransitivity; [ apply IHn | reflexivity ].
Qed.

Lemma counting_wins p q :
  q < p ->
  filter winb (filter (sumtrue p) (pickbools (p + q))) =
  filter (sumtrue p) (pickbools (p + q)).
Proof.
  intros. rewrite pickbools_length.
  repeat rewrite filter_filter. apply filter_ext.
  intros x. unfold winb, sumtrue.
  destruct (length x =? p + q) eqn:E. 2:reflexivity. simpl.
  destruct (countb true x =? p) eqn:E2. 2:reflexivity. simpl.
  rewrite countb_false.
  rewrite Nat.ltb_lt.
  rewrite Nat.eqb_eq in *.
  omega.
Qed.

Lemma pickbools_wins_minus p q :
  q <= p ->
  (p - q) * length (filter (sumtrue p) (pickbools (p + q))) =
  (p - q) * length (filter winb (filter (sumtrue p) (pickbools (p + q)))).
Proof.
  intros L.
  assert (D : q = p \/ q < p) by omega. destruct D as [D | D].
  - replace (p - q) with 0 by omega. omega.
  - clear L. f_equal. f_equal. rewrite counting_wins; auto.
Qed.
  
Lemma bertrand_ballot_bool_eq p q :
  p <> 0 ->
  p = q ->
  let l := filter (fun votes => countb true votes =? p) (pickbools (p + q)) in
  (p + q) * length (filter (throughout winb) l) =
  (p - q) * length (filter winb l).
Proof.
  intros L <-. replace (p - p) with 0 by omega. simpl.
  match goal with |- ?a * ?b = 0 => cut (b = 0) end. intros ->; auto.
  rewrite pickbools_length.
  transitivity (length (filter (fun _ => false) (pickbools (p + p)))).
  - f_equal. rewrite pickbools_length. repeat rewrite filter_filter.
    apply filter_ext. intros x.
    destruct (length x =? p + p) eqn:Hlen; auto. simpl.
    destruct (countb true x =? p) eqn:Hp; auto. simpl.
    rewrite Nat.eqb_eq in *.
    destruct x. simpl in *. omega.
    unfold throughout. simpl.
    unfold winb. rewrite countb_false.
    rewrite Hlen, Hp.
    replace (p + p - p) with p by omega.
    rewrite Nat.ltb_irrefl.
    reflexivity.
  - generalize (pickbools (p + p)). generalize (list bool). clear.
    intros P l.
    induction l; auto.
Qed.

Theorem bertrand_ballot_bool p q :
  q <= p ->
  let l := filter (sumtrue p) (pickbools (p + q)) in
  (p + q) * length (filter (throughout winb) l) =
  (p - q) * length (filter winb l).
Proof.
  intros L l.
  
  remember (p + q) as n.
  revert p q L Heqn l.
  induction n; intros p q L Heqn l.
  
  (** the case n = 0 is easy *)
  { assert (p = 0) by omega. assert (q = 0) by omega. subst; simpl. reflexivity. }

  (** the case p = q is easy *)
  assert (D : q = p \/ q < p) by omega. destruct D as [D | D].
  { subst l. rewrite Heqn.
    destruct p as [ | p ]. subst; reflexivity.
    apply (bertrand_ballot_bool_eq (S p) q); auto. }
  
  (** case p > q *)
  destruct p as [ | p]; [ | destruct q as [ | q ] ].
  
  - (** case p = 0: trivial because p > q *)
    omega.
  
  - (** case q = 0 *)
    assert (n = p) by omega; subst n. f_equal.
    subst l. clear. f_equal. rewrite pickbools_length.
    repeat rewrite filter_filter. apply filter_ext. intros x.
    destruct (length x =? S p) eqn:El. 2:reflexivity.
    destruct (sumtrue (S p) x) eqn:Ep. 2:reflexivity. simpl.
    unfold sumtrue in Ep.
    rewrite Nat.eqb_eq in *.
    assert (F : countb false x = 0).
    { rewrite countb_false. omega. }
    assert (E : forall x, length x <> 0 -> countb false x = 0 -> winb x = true).
    { clear. intros. unfold winb. rewrite Nat.ltb_lt.
      rewrite countb_false in *. omega. }
    rewrite E; auto. 2:omega.
    assert (E' : forall x, length x <> 0 -> countb false x = 0 -> throughout winb x = true).
    {
      unfold throughout.
      clear -E. intros x L F. induction x as [| [ | ] l IHl].
      - tauto.
      - simpl.
        rewrite E; try omega.
        destruct l as [ | [ | ] l ].
        + reflexivity.
        + apply IHl. simpl. omega. auto.
        + discriminate.
      - discriminate.
    }
    apply E'. omega. auto.
  
  - (** case p, q > 0 *)
    pose proof IHn (S p) q ltac:(omega) ltac:(omega) as Hsp.
    pose proof IHn p (S q) ltac:(omega) ltac:(omega) as Hp.
    clear IHn.
    
    replace (filter winb l) with l; swap 1 2.
    { subst l. rewrite Heqn. rewrite counting_wins; auto. }
    rewrite Heqn.
    eapply recurrence; try omega; swap 1 3; swap 2 6.
    { subst l. rewrite Heqn. rewrite first_vote_split.
      rewrite app_length. reflexivity. }
    { subst l. rewrite Heqn. rewrite first_vote_split.
      rewrite filter_app. do 2 rewrite map_filter.
      rewrite app_length. reflexivity. }
    + (* binomial things *)
      subst l.
      rewrite Heqn. clear.
      rewrite map_length. do 2 rewrite count_sumtrue.
      simpl (_ + _).
      assert (L : p <= p + S q) by omega. revert L.
      generalize (p + S q); intros n L.
      apply binomial_S. auto.
    
    + (* throughout winnning, last vote being a true *)
      injection Heqn as ->.
      clear Hsp l.
      simpl in Hp.
      do 2 rewrite map_length.
      replace (S p - 1 + S q) with (p + S q) by omega.
      replace (S p - S q - 1) with (p - S q) by omega.
      rewrite pickbools_wins_minus. 2:omega.
      rewrite <-Hp. clear Hp.
      f_equal.
      f_equal.
      repeat rewrite filter_filter.
      apply filter_ext; intros x.
      f_equal. unfold throughout. simpl.
      destruct x. simpl. reflexivity.
      simpl. rewrite Bool.andb_assoc. f_equal.
      generalize (b :: x); clear; intros l.
      unfold winb. simpl.
      generalize (countb false l).
      generalize (countb true l). clear.
      intros a b.
      destruct (b <? a) eqn:Ea, (b <? S a) eqn:Esa; auto.
      rewrite Nat.ltb_lt in *.
      rewrite Nat.ltb_nlt in *.
      omega.
    
    + (* throughout winnning, last vote being a false *)
      injection Heqn as ->. clear Hp l.
      replace (S p - 1 + S q) with (p + S q) by omega.
      replace (S p - (S q - 1)) with (S p - q) by omega.
      do 2 rewrite map_length.
      replace ((S p - q) * length (filter (sumtrue (1 + p)) (pickbools (p + S q))))
      with ((S p - q) * length (filter winb (filter (sumtrue (1 + p)) (pickbools (p + S q))))); swap 1 2.
      { replace (p + S q) with (S p + q) by omega.
        rewrite pickbools_wins_minus. 2:omega. auto. }
      simpl in *.
      rewrite <-Hsp.
      f_equal.
      f_equal.
      rewrite pickbools_length.
      repeat rewrite filter_filter.
      apply filter_ext; intros x.
      clear Hsp.
      destruct (length x =? p + S q) eqn:Hlen. 2:reflexivity. simpl.
      destruct (sumtrue (S p) x) eqn:Hp. 2:reflexivity. simpl.
      unfold throughout. simpl.
      rewrite Bool.andb_comm.
      destruct (forallb winb (proper_suffixes x)) eqn:Hw. 2:reflexivity. simpl.
      unfold winb.
      unfold sumtrue in Hp.
      repeat rewrite Nat.ltb_lt in *.
      repeat rewrite Nat.eqb_eq in *.
      simpl.
      rewrite countb_false.
      omega.
    
    + (* binomial things *)
      subst l.
      rewrite Heqn. clear.
      rewrite map_length. do 2 rewrite count_sumtrue.
      simpl (_ + _).
      replace (S q) with (p + S q - p) at 3 by omega.
      assert (L : p <= p + S q) by omega. revert L.
      generalize (p + S q); intros n L.
      assert (D : p = n \/ p < n) by omega. destruct D as [D | D].
      * subst p. rewrite binomial_lt. rewrite binomial_diag. omega. omega.
      * rewrite binomial_complement. 2:omega.
        rewrite (binomial_complement (S n)). 2:omega.
        rewrite (binomial_S n (n - S p)). 2:omega.
        f_equal. omega.
        f_equal. omega.
Qed.

Definition count_votes := count_occ string_dec.

Definition wins A B votes := count_votes votes B <? count_votes votes A.

Open Scope string_scope.

(** we enumerate all lists of votes with:
     - p + q votes for (A or B)
     - p votes for A   *)

Theorem bertrand_ballot p q :
  let l := filter (fun votes => count_votes votes "A" =? p) (picks (p + q) ["A"; "B"]) in
  p >= q ->
  (p + q) * List.length (filter (throughout (wins "A" "B")) l) =
  (p - q) * List.length (filter (wins "A" "B") l).
Proof.
  intros l L; subst l.
  pose (f := fun b : bool => if b then "A" else "B").
  replace (picks (p + q) ["A"; "B"]) with (map (map f) (pickbools (p + q))); swap 1 2.
  {
    generalize (p + q). clear p q L. induction n. reflexivity.
    simpl. do 2 rewrite map_app. f_equal. 2:rewrite app_nil_r.
    all: rewrite <- IHn.
    all: generalize (pickbools n); intros l; induction l; simpl; congruence.
  }
  
  repeat rewrite map_filter.
  repeat rewrite map_length.
  
  assert (A : forall b l, count_votes (map f l) (f b) = countb b l).
  { clear. intros b l; induction l; auto. simpl.
    destruct a, b; simpl; auto. }
  assert (E : forall l, wins "A" "B" (map f l) = winb l).
  { clear -A. unfold wins, winb. intros l. f_equal. apply (A false). apply (A true). }
  
  etransitivity; [ | etransitivity ]; [ | apply (bertrand_ballot_bool p q); auto | ]; f_equal.
  - f_equal.
    repeat rewrite filter_filter.
    apply filter_ext.
    intros l. f_equal.
    + unfold sumtrue. f_equal.
      induction l as [ | b l IHl]; auto. simpl. destruct b; auto. simpl. auto.
    + unfold throughout, proper_suffixes.
      induction l as [ | b l IHl]; auto.
      simpl. f_equal; auto.
      rewrite <-E. auto.
  - f_equal.
    repeat rewrite filter_filter.
    apply filter_ext.
    intros l; f_equal. 2:now auto.
    unfold sumtrue. f_equal. rewrite <-A. auto.
Qed.

