Require Import Arith.
Require Import ZArith.
Require Import List.
Import ListNotations.

Fixpoint appears x l :=
  match l with
  | [] => false
  | y :: l => if beq_nat x y then true else appears x l
  end.

Fixpoint collision l :=
  match l with
  | [] => false
  | x :: l => if appears x l then true else collision l
  end.

Fixpoint enumerate n :=
  match n with
  | 0 => []
  | S n => n :: enumerate n
  end.

Lemma length_enumerate n : length (enumerate n) = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma filter_app {A} f (l1 l2 : list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [| a l IHl]; simpl. reflexivity.
  destruct (f a); simpl; congruence.
Qed.

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

Lemma length_cartesian_product {A B} (xs : list A) (ys : list B) :
  length (cartesian_product xs ys) = length xs * length ys.
Proof.
  induction xs. reflexivity. simpl.
  rewrite app_length, map_length. congruence.
Qed.

Lemma Zlength_picks {A} n (l : list A) :
  Zlength (picks n l) = Z.pow (Zlength l) (Z.of_nat n).
Proof.
  rewrite Zlength_correct.
  induction n. reflexivity. simpl (length _).
  rewrite map_length, length_cartesian_product.
  change (S n) with (1 + n).
  rewrite Nat2Z.inj_add, Z.pow_add_r, Z.pow_1_r.
  rewrite <-IHn.
  rewrite Nat2Z.inj_mul, Zlength_correct.
  reflexivity.
  all: zify; omega.
Qed.

Fixpoint partial_fact k n (* = n! / (n-k)! *) :=
  (match k with
   | O => 1
   | S k => n * partial_fact k (n - 1)
   end)%Z.

Definition no {A} (f : A -> bool) x := negb (f x).

Lemma cartesian_product_filters {A B} (f : A -> bool) (g : B -> bool) xs ys :
  cartesian_product (filter f xs) (filter g ys) =
  filter (fun p => andb (f (fst p)) (g (snd p))) (cartesian_product xs ys).
Proof.
  revert ys.
  induction xs; intros ys; auto.
  simpl.
  rewrite filter_app.
  rewrite <-IHxs.
  destruct (f a) eqn:Ha.
  - simpl. f_equal.
    clear -Ha.
    induction ys as [| b ys IHys]; auto.
    simpl. destruct (f a), (g b); simpl; congruence.
  - rewrite IHxs.
    match goal with |- ?a = _ => transitivity ([] ++ a) end. reflexivity.
    f_equal.
    induction ys as [| b ys IHys]; auto.
    simpl. destruct (f a), (g b); simpl; try congruence.
Qed.

Lemma picks_remove k a l :
  picks k (filter (no (Nat.eqb a)) l) =
  filter (no (appears a)) (picks k l).
Proof.
  induction k. reflexivity.
  simpl. rewrite IHk. clear IHk.
  generalize (picks k l); intros ll.
  rewrite cartesian_product_filters.
  induction (cartesian_product l ll) as [| a0 l0 IHl0]. simpl. reflexivity.
  simpl.
  rewrite <-IHl0.
  unfold no.
  simpl.
  destruct (a =? fst a0). reflexivity.
  simpl.
  destruct (appears a (snd a0)); reflexivity.
Qed.

Lemma appears_filter x l f :
  appears x l = false -> appears x (filter f l) = false.
Proof.
  induction l. reflexivity.
  simpl.
  destruct (f a); simpl; destruct (x =? a); auto.
  discriminate.
Qed.

Lemma collision_filter l f :
  collision l = false -> collision (filter f l) = false.
Proof.
  induction l. reflexivity.
  simpl.
  destruct (appears a l) eqn:E1. discriminate.
  intros E2.
  destruct (f a). simpl in *. rewrite appears_filter; auto.
  auto.
Qed.

Lemma collision_count l :
  collision l = false -> Forall (fun x1 : nat => count_occ Nat.eq_dec l x1 = 1) l.
Proof.
  change (collision ([] ++ l) = false -> Forall (fun x1 : nat => count_occ Nat.eq_dec ([] ++ l) x1 = 1) l).
  generalize ([] : list nat).
  induction l; intros pre Hcol. constructor.
  constructor.
  - clear -Hcol.
    induction pre as [| b pre IHpre].
    + simpl in *.
      destruct (Nat.eq_dec a a) as [ _ | ]; [ | tauto ].
      f_equal.
      destruct (appears a l) eqn:Ha. discriminate. clear Hcol.
      induction l as [|b l IHl]. reflexivity. simpl.
      destruct (Nat.eq_dec b a).
      * subst. simpl in Ha. rewrite <-beq_nat_refl in Ha. discriminate.
      * apply IHl. simpl in Ha. destruct (a =? b); auto; discriminate.
    + simpl in *.
      destruct (appears b (pre ++ a :: l)) eqn:Eb. discriminate.
      rewrite IHpre; auto.
      destruct (Nat.eq_dec b a); auto. subst.
      cut (appears a (pre ++ a :: l) = true). congruence. clear.
      induction pre as [|b pre IHpre]. simpl. rewrite <-beq_nat_refl. reflexivity.
      simpl. destruct (a =? b); auto.
  - assert (E : pre ++ a :: l = (pre ++ a :: nil) ++ l).
    { rewrite <-app_assoc. reflexivity. }
    rewrite E. apply IHl. congruence.
Qed.

Lemma length_no_collision_picks k l :
  collision l = false ->
  Zlength (filter (no collision) (picks k l)) =
  partial_fact k (Zlength l).
Proof.
  rewrite Zlength_correct.
  revert l; induction k; intros l Hcol. reflexivity.
  simpl.
  set (l1 := l) at 1 3.
  assert (Huniq : Forall (fun x1 => count_occ Nat.eq_dec l x1 = 1) l1).
  { apply collision_count; auto. }
  clearbody l1.
  induction l1 as [| a l1 IHl1]. reflexivity.
  simpl.
  rewrite map_app, filter_app, app_length.
  rewrite Zlength_cons, Z.mul_succ_l, Nat2Z.inj_add.
  rewrite Z.add_comm. f_equal.
  - rewrite IHl1. auto.
    inversion Huniq; auto.
  - clear IHl1.
    rewrite map_map. simpl.
    pose (l' := filter (no (beq_nat a)) l).
    assert (El' : Zlength l' = (Zlength l - 1)%Z).
    {
      apply Forall_inv in Huniq.
      cut (Zlength l' + 1 = Zlength l)%Z.
      { intros <-. omega. }
      unfold l'.
      do 2 rewrite Zlength_correct.
      change 1%Z with (Z.of_nat 1).
      rewrite <-Nat2Z.inj_add.
      f_equal.
      rewrite <-Huniq.
      clear IHk k Hcol l' Huniq.
      induction l as [| b l IHl]. reflexivity. simpl.
      rewrite <-IHl.
      unfold no.
      destruct (Nat.eq_dec b a).
      - subst. rewrite <-beq_nat_refl. simpl. omega.
      - replace (a =? b) with false; simpl. reflexivity.
        symmetry. apply Nat.eqb_neq. auto.
    }
    assert (Hl' : collision l' = false).
    {
      unfold l'. generalize (no (Nat.eqb a)); intros f.
      clear -Hcol.
      apply collision_filter; auto.
    }
    rewrite <-El'.
    rewrite <-IHk; auto.
    f_equal.
    transitivity (length (map (fun x => a :: x) (filter (no collision) (picks k l')))).
    2: rewrite map_length; reflexivity.
    f_equal.
    unfold l'.
    apply Forall_inv in Huniq.
    clear IHk El' l' Hl' l1.
    rewrite picks_remove.
    induction (picks k l) as [| l' ll' IHll']. reflexivity.
    simpl.
    unfold no at 1 5.
    simpl.
    destruct (appears a l'). simpl; congruence.
    simpl.
    unfold no at 3.
    destruct (collision l'); simpl; congruence.
Qed.

Lemma length_filter {A} (f : A -> bool) l :
  length (filter f l) + length (filter (no f) l) = length l.
Proof.
  unfold no.
  induction l; auto. simpl.
  destruct (f a); simpl; omega.
Qed.

Lemma Zlength_filter {A} (f : A -> bool) l :
  (Zlength (filter f l) = Zlength l - Zlength (filter (no f) l))%Z.
Proof.
  repeat rewrite Zlength_correct.
  rewrite <-(length_filter f l).
  zify. omega.
Qed.

Lemma enumerate_no_collisions n : collision (enumerate n) = false.
Proof.
  induction n. reflexivity. simpl. rewrite IHn.
  cut (forall a b, a <= b -> appears b (enumerate a) = false).
  { intros ->; auto. }
  clear.
  intros a. induction a; intros b Hb.
  - reflexivity.
  - simpl. rewrite IHa. 2:omega.
    replace (b =? a) with false; auto.
    symmetry.
    apply Nat.eqb_neq.
    omega.
Qed.

Theorem birthday_paradox :
  let l := picks 23 (enumerate 365) in
  2 * length (filter collision l) > length l.
Proof.
  intros l; unfold l.
  apply Nat2Z.inj_lt.
  rewrite Nat2Z.inj_mul.
  repeat rewrite <-Zlength_correct.
  rewrite Zlength_filter.
  rewrite length_no_collision_picks. 2:apply enumerate_no_collisions.
  repeat rewrite Zlength_picks.
  reflexivity.
Qed.

Theorem birthday_paradox_min :
  let l := picks 22 (enumerate 365) in
  2 * length (filter collision l) < length l.
Proof.
  intros l; unfold l.
  apply Nat2Z.inj_lt.
  rewrite Nat2Z.inj_mul.
  repeat rewrite <-Zlength_correct.
  rewrite Zlength_filter.
  rewrite length_no_collision_picks. 2:apply enumerate_no_collisions.
  repeat rewrite Zlength_picks.
  reflexivity.
Qed.
