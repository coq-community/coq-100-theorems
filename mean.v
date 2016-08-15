(* Tested with Coq 8.5pl2 *)
Require Import Omega Reals Psatz.

Open Scope R_scope.

Tactic Notation "assert_specialize" hyp(H) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp; [ | specialize (H Htemp); try clear Htemp ]
  end.

Tactic Notation "assert_specialize" hyp(H) "by" tactic(tac) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp by tac; specialize (H Htemp); try clear Htemp
  end.

Ltac exact_eq H :=
  revert H;
  match goal with
    |- ?p -> ?q => cut (p = q); [intros ->; auto | ]
  end.

Lemma base x y : 4 * (x * y) <= (x + y) * (x + y).
Proof.
  apply Rminus_le.
  apply Rle_trans with (- (x - y) ^ 2).
  - now ring_simplify; auto with *.
  - apply Rge_le, Ropp_0_le_ge_contravar, pow2_ge_0.
Qed.

Lemma base' x y : (x * y) <= (x + y) * (x + y) / 4.
Proof.
  pose proof base x y as L.
  apply Rmult_le_compat_r with (r := / 4) in L. 2:lra.
  refine (Rle_trans _ _ _ _ L). apply Req_le.
  rewrite (Rmult_comm _ (/ 4)), <-Rmult_assoc, (Rmult_comm _ 4).
  rewrite Rinv_r. ring. lra.
Qed.

Lemma base_strict x y : x <> y -> 4 * (x * y) < (x + y) * (x + y).
Proof.
  intros ne.
  apply Rminus_lt.
  apply Rle_lt_trans with (- (x - y) ^ 2).
  - now ring_simplify; auto with *.
  - apply Rgt_lt, Ropp_0_lt_gt_contravar.
    assert (H : 0 <> x - y) by lra; revert H.
    generalize (x - y); clear.
    intros r n.
    destruct (Rdichotomy _ _ n) as [p|p].
    + replace (r ^ 2) with (r * r) by ring.
      apply Rmult_lt_0_compat; auto.
    + replace (r ^ 2) with (- r * - r) by ring.
      apply Rmult_lt_0_compat; auto with *.
Qed.

Lemma mean2 x y :
  0 <= x ->
  0 <= y ->
  sqrt (x * y) <= (x + y) / 2.
Proof.
  assert (MP : forall x y, 0 <= x -> 0 <= y -> 0 <= x * y).
  {
    intros. replace 0 with (0 * 0) by ring.
    apply Rmult_le_compat; auto with *.
  }
  assert (AP : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y) by (intros; lra).
  assert (0 <= 4) by lra.
  
  intros px py.
  pose proof base x y as L.
  apply sqrt_le_1 in L.
  rewrite sqrt_mult in L.
  do 2 rewrite sqrt_square in L.
  apply Rmult_le_compat_r with (r := / 2) in L.
  refine (Rle_trans _ _ _ _ L); clear L; apply Req_le.
  replace (2 * sqrt (x * y) * / 2)
  with ((2 * / 2) * sqrt (x * y)) by ring.
  rewrite Rinv_r.

  (* solving side conditions *)
  all: auto with *; lra.
Qed.

Lemma mean2_strict x y :
  0 <= x ->
  0 <= y ->
  x <> y ->
  sqrt (x * y) < (x + y) / 2.
Proof.
  assert (MP : forall x y, 0 <= x -> 0 <= y -> 0 <= x * y).
  {
    intros. replace 0 with (0 * 0) by ring.
    apply Rmult_le_compat; auto with *.
  }
  assert (AP : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y) by (intros; lra).
  assert (0 <= 4) by lra.
  
  intros px py n.
  pose proof base_strict x y n as L.
  apply sqrt_lt_1 in L.
  rewrite sqrt_mult in L.
  do 2 rewrite sqrt_square in L.
  apply Rmult_lt_compat_r with (r := / 2) in L.
  refine (Rle_lt_trans _ _ _ _ L); clear L; apply Req_le.
  replace (2 * sqrt (x * y) * / 2)
  with ((2 * / 2) * sqrt (x * y)) by ring.
  rewrite Rinv_r. ring.

  (* solving side conditions *)
  all: auto with *; lra.
Qed.


Lemma mean2_ge x y :
  0 <= x ->
  0 <= y ->
  sqrt (x * y) >= (x + y) / 2 ->
  x = y.
Proof.
  intros px py.
  pose proof mean2_strict _ _ px py; lra.
Qed.

Lemma mean2_rev x y :
  0 <= x ->
  0 <= y ->
  sqrt (x * y) = (x + y) / 2 ->
  x = y.
Proof.
  intros px py.
  pose proof mean2_ge _ _ px py.
  lra.
Qed.

Lemma Rdiv_fold x y : x * / y = x / y. reflexivity. Qed.

Lemma mean_aux x1 y1 x2 y2 :
  0 <= x1 -> 0 <= y1 -> 
  x1 <= x2 -> y1 <= y2 ->
  sqrt (x1 * y1) = (x2 + y2) / 2 ->
  x1 = x2 /\ y1 = y2 /\ x1 = y1.
Proof.
  intros px py lx ly E.
  assert (sqrt (x1 * y1) <= sqrt (x2 * y2)).
  { apply sqrt_le_1; try apply Rmult_le_pos; auto.
    - apply Rle_trans with x1; eauto.
    - apply Rle_trans with y1; eauto.
    - apply Rmult_le_compat; eauto. }
  pose proof mean2 x1 y1 px py.
  pose proof mean2 x2 y2 ltac:(lra) ltac:(lra).
  pose proof mean2_ge x1 y1 px py ltac:(lra).
  pose proof mean2_ge x2 y2 ltac:(lra) ltac:(lra) ltac:(lra).
  subst y1 y2.
  change (x1 * x1) with (x1 ²) in E.
  rewrite sqrt_Rsqr in E; auto.
  unfold Rdiv in E.
  rewrite Rmult_plus_distr_r in E.
  rewrite Rdiv_fold in E.
  rewrite <-double_var in E.
  auto.
Qed.

Definition shift {X} n (u : nat -> X) : nat -> X := fun i => u (plus i n).

Fixpoint sum n u := match n with O => 0 | S n => u O + sum n (shift 1 u) end.

Fixpoint prod n u := match n with O => 1 | S n => u O * prod n (shift 1 u) end.

Fixpoint pow2 n := (match n with O => 1 | S n => 2 * pow2 n end)%nat.

Lemma sum_ext n u v : (forall x, u x = v x) -> sum n u = sum n v.
Proof.
  revert u v; induction n. auto.
  intros u v E; simpl; rewrite E; f_equal; apply IHn.
  intro; apply E.
Qed.

Lemma prod_ext n u v : (forall x, u x = v x) -> prod n u = prod n v.
Proof.
  revert u v; induction n. auto.
  intros u v E; simpl; rewrite E; f_equal; apply IHn.
  intro; apply E.
Qed.

Lemma sum_ext_lt n u v : (forall i, lt i n -> u i = v i) -> sum n u = sum n v.
Proof.
  revert u v; induction n. auto.
  intros u v E; simpl; rewrite E; auto with *. f_equal. apply IHn.
  intros i Hi. apply E. omega.
Qed.

Lemma prod_ext_lt n u v : (forall i, lt i n -> u i = v i) -> prod n u = prod n v.
Proof.
  revert u v; induction n. auto.
  intros u v E; simpl; rewrite E; auto with *. f_equal. apply IHn.
  intros i Hi. apply E. omega.
Qed.

Lemma sum_plus n m u : sum (n + m) u = sum n u + sum m (shift n u).
Proof.
  revert u; induction n; intros u; simpl.
  - ring_simplify.
    apply sum_ext; compute; auto.
  - rewrite IHn. ring_simplify.
    f_equal. apply sum_ext; intros; unfold shift.
    f_equal; auto with *.
Qed.

Lemma prod_plus n m u : prod (n + m) u = prod n u * prod m (shift n u).
Proof.
  revert u; induction n; intros u; simpl.
  - ring_simplify.
    apply prod_ext; compute; auto.
  - rewrite IHn. ring_simplify.
    f_equal. apply prod_ext; intros; unfold shift.
    f_equal; auto with *.
Qed.

Lemma prod_pos n u : (forall i, 0 <= u i) -> 0 <= prod n u.
Proof.
  revert u; induction n; auto; intros u p; simpl. lra.
  apply Rmult_le_pos; auto.
  apply IHn. intro; apply p.
Qed.

Lemma sum_pos n u : (forall i, 0 <= u i) -> 0 <= sum n u.
Proof.
  revert u; induction n; auto; intros u p; simpl. lra.
  specialize (IHn (shift 1 u)).
  assert_specialize IHn. intro; apply p. specialize (p O). lra.
Qed.

Lemma sum_pos_lt n u : (forall i, lt i n -> 0 <= u i) -> 0 <= sum n u.
Proof.
  revert u; induction n; auto; intros u p; simpl. lra.
  specialize (IHn (shift 1 u)).
  assert_specialize IHn. intros i Hi; apply p. omega.
  specialize (p O). assert_specialize p by omega. lra.
Qed.

Definition sqrtk k := Nat.iter k sqrt.

Lemma sqrtk_pos k a : 0 <= a -> 0 <= sqrtk k a.
Proof.
  destruct k; auto. intro; apply sqrt_pos.
Qed.

Lemma sqrtk_mult k a b : 0 <= a -> 0 <= b -> sqrtk k (a * b) = sqrtk k a * sqrtk k b.
Proof.
  intros pa pb; induction k; simpl; auto.
  rewrite <-sqrt_mult; try apply sqrtk_pos; auto.
  f_equal; assumption.
Qed.

Lemma pow2_sqrtk k a : 0 <= a -> pow (sqrtk k a) (pow2 k) = a.
Proof.
  intros p; induction k; simpl. ring.
  rewrite <-IHk at 2; clear IHk.
  replace (pow2 k + (pow2 k + 0))%nat with (2 * pow2 k)%nat by ring.
  rewrite pow_mult. f_equal. simpl. rewrite <-Rmult_assoc.
  rewrite sqrt_sqrt. ring. apply sqrtk_pos, p.
Qed.

Lemma sqrtk_pow2 k a : 0 <= a -> sqrtk k (pow a (pow2 k)) = a.
Proof.
  intros p; induction k; simpl. ring.
  rewrite <-IHk at 2; clear IHk.
  replace (pow2 k + (pow2 k + 0))%nat with (pow2 k * 2)%nat by ring.
  rewrite pow_mult. simpl. rewrite Rmult_1_r, sqrtk_mult, sqrt_square. auto.
  apply sqrtk_pos. all:apply pow_le; auto.
Qed.

Lemma INR_pow2 k : 0 < INR (pow2 k).
Proof.
  induction k; simpl. lra.
  do 2 rewrite plus_INR. simpl. lra.
Qed.

Lemma mean_power_of_two a :
  (forall i, 0 <= a i) ->
  forall k,
    sqrtk k (prod (pow2 k) a) <=
    sum (pow2 k) a / INR (pow2 k).
Proof.
  intros pa k; revert a pa; induction k; intros a pa; simpl. lra.
  remember (pow2 k) as n.
  assert (R : (n + (n + 0) = n + n)%nat) by ring; rewrite R; clear R.
  rewrite prod_plus.
  rewrite sum_plus.
  pose proof IHk a pa as L.
  pose proof IHk (shift n a) ltac:(intros; apply pa) as R.
  clear IHk.
  eapply Rle_trans.
  - rewrite sqrtk_mult. all:try (apply prod_pos; intros; apply pa).
    apply mean2. all: apply sqrtk_pos, prod_pos; intros; apply pa.
  - unfold Rdiv. do 2 rewrite Rmult_plus_distr_r.
    replace (INR (n + n)) with (INR (n * 2)) by (f_equal; ring).
    rewrite mult_INR, (Rinv_mult_distr (INR n)).
    do 2 rewrite <-Rmult_assoc with (r3 := / INR 2).
    replace (INR 2) with 2.
    apply Rplus_le_compat; apply Rmult_le_compat; auto.
    all: simpl; try lra.
    all: try (apply sqrtk_pos, prod_pos; intros; apply pa).
    pose proof INR_pow2 k. subst. lra.
Qed.

Lemma mean_power_of_two_eq a :
  (forall i, 0 <= a i) ->
  forall k,
    sqrtk k (prod (pow2 k) a) = sum (pow2 k) a / INR (pow2 k) ->
    forall i j, lt i (pow2 k) -> lt j (pow2 k) -> a i = a j.
Proof.
  intros pa k E.
  cut (forall i, lt i (pow2 k) -> a i = sum (pow2 k) a / INR (pow2 k)).
  { intros C i j Hi Hj. rewrite (C i Hi), (C j Hj). auto. }
  revert a pa E; induction k; intros a pa; simpl.
  - intros E i Hi. inversion Hi. field. omega.
  - remember (pow2 k) as n.
    assert (R : (n + (n + 0) = n + n)%nat) by ring; rewrite R; clear R.
    rewrite prod_plus, sum_plus.
    pose proof IHk a pa as HL.
    pose proof IHk (shift n a) ltac:(intros; apply pa) as HR.
    clear IHk.
    intros E.
    pose proof mean_power_of_two a pa k as L1.
    pose proof mean_power_of_two (shift n a) ltac:(intro; apply pa) k as R1.
    rewrite <-Heqn in *.
    rewrite sqrtk_mult in E; try (apply prod_pos; intro; apply pa).
    replace (n + n)%nat with (n * 2)%nat in E |- *. 2:omega.
    rewrite mult_INR in E |- *.
    assert (dhalf : forall x, (x + x) / 2 = x).
    { intros x; unfold Rdiv. rewrite Rmult_plus_distr_r, Rdiv_fold, <-double_var. auto. }
    unfold Rdiv in E |- *.
    assert (INR n <> 0).
    { assert (n <> O). subst. clear; induction k; simpl; auto. omega. auto with *. }
    rewrite Rinv_mult_distr in E |- *; auto with *.
    rewrite <-Rmult_assoc, Rmult_plus_distr_r in E |- *.
    repeat rewrite Rdiv_fold in *.
    remember (sqrtk k (prod n a)) as g1 eqn:Eg1.
    remember (sqrtk k (prod n (shift n a))) as g2 eqn:Eg2.
    remember (sum n a / INR n) as a1 eqn:Ea1.
    remember (sum n (shift n a) / INR n) as a2 eqn:Ea2.
    pose proof mean_aux g1 g2 a1 a2 as Rec.
    do 2 assert_specialize Rec by (subst; apply sqrtk_pos, prod_pos; intro; apply pa).
    repeat assert_specialize Rec by auto.
    assert_specialize HR by intuition.
    assert_specialize HL by intuition.
    replace a2 with a1 in * by intuition congruence.
    replace (INR 2) with 2 by (compute; ring).
    rewrite dhalf.
    clear -HL HR.
    intros i li.
    assert (D : (i < n \/ i >= n)%nat) by omega. destruct D as [D|D].
    + apply HL, D.
    + specialize (HR (i - n)%nat ltac:(omega)).
      exact_eq HR; f_equal.
      unfold shift; f_equal.
      omega.
Qed.

Theorem geometric_arithmetic_mean (a : nat -> R) (n : nat) :
  n <> O ->
  (forall i, (i < n)%nat -> 0 <= a i) ->
  prod n a <= (sum n a / INR n) ^ n
  /\
  (prod n a = (sum n a / INR n) ^ n -> forall i, (i < n)%nat -> a i = a O).
Proof.
  assert (H : exists k, lt n (pow2 k)).
  { exists n. induction n; simpl; omega. }
  intros p pa. destruct H as (k, Hk).
  
  set (alpha := sum n a / INR n).
  
  assert (na0 : alpha = 0 -> forall i, lt i n -> a i = 0). {
    intros a0. remember alpha as al eqn:E. unfold alpha in E. clear alpha.
    assert (s : sum n a = 0).
    - replace (sum n a) with (al * INR n). rewrite a0. ring.
      rewrite E. field. auto with *.
    - clear -s pa; revert a s pa.
      induction n; intros a s pa.
      + intros i Hi; inversion Hi.
      + cut (a O = 0 /\ sum n (shift 1 a) = 0).
        * intros (a0, s0) i Hi.
          specialize (IHn _ s0).
          assert_specialize IHn.
          { intros; apply pa; omega. }
          destruct i. apply a0.
          specialize (IHn i).
          assert_specialize IHn. omega.
          rewrite <-IHn. unfold shift. f_equal. omega.
        * simpl in s.
          apply Rplus_eq_R0; auto with *.
          apply sum_pos_lt. intros i Hi; specialize (pa (S i)).
          assert_specialize pa. omega.  exact_eq pa. f_equal.
          unfold shift. f_equal. omega.
  }
  
  assert (0 <= alpha). {
    unfold alpha. clear alpha na0.
    apply Rmult_le_pos; auto with *.
    apply sum_pos_lt; auto.
  }
  
  set (b := fun i => if le_lt_dec n i then alpha else a i).
  assert (pb : forall i, 0 <= b i). {
    intros i; unfold b.
    destruct (le_lt_dec n i); auto.
  }
  
  assert (R : prod (pow2 k) b = prod n a * alpha ^ (pow2 k - n)).
  {
    replace (pow2 k) with (n + (pow2 k - n))%nat at 1 by omega.
    rewrite prod_plus. f_equal.
    - apply prod_ext_lt. intros j Hj. unfold b.
      destruct (le_lt_dec n j). omega. auto.
    - generalize (pow2 k - n)%nat as v; intros v.
      assert (L : le n n) by auto; revert L.
      generalize n at 2 3.
      induction v; intros n0 ln0. auto. simpl. f_equal.
      + unfold shift, b. simpl. destruct (le_lt_dec n n0). auto. omega.
      + rewrite <-(IHv (plus 1 n0)); auto with *.
        apply prod_ext. intros x. unfold shift. f_equal. omega.
  }
  
  assert (IH : sum (pow2 k) b / INR (pow2 k) = alpha). {
    cut (sum (pow2 k) b = alpha * INR (pow2 k)).
    { intros ->. field. auto with *. }
    replace (pow2 k) with (n + (pow2 k - n))%nat. 2:omega.
    rewrite sum_plus. rewrite plus_INR. rewrite Rmult_plus_distr_l.
    f_equal.
    - unfold alpha. transitivity (sum n a).
      + apply sum_ext_lt. intros i Hi; unfold b.
        destruct (le_lt_dec n i). omega. auto.
      + field. auto with *.
    - generalize (pow2 k - n)%nat as v; intros v.
      assert (L : le n n) by auto; revert L.
      generalize n at 2 3.
      induction v; intros n0 ln0. simpl; ring. simpl sum.
      change (S v) with (plus 1 v). rewrite plus_INR.
      rewrite Rmult_plus_distr_l. f_equal.
      + unfold shift, b. simpl. destruct (le_lt_dec n n0). ring. omega.
      + rewrite <-(IHv (plus 1 n0)); auto with *.
        apply sum_ext. intros x. unfold shift. f_equal. omega.
  }
  
  split.
  
  - (* inequality *)
    Ltac wlog P :=  match goal with |- ?Q => cut (P -> Q) end.
    wlog (0 < alpha). {
      intros wlog.
      destruct H; auto.
      assert_specialize na0; auto.
      apply Req_le. transitivity 0.
      - destruct n. tauto. simpl. rewrite na0; auto with *.
      - destruct n. tauto. simpl. rewrite <-H. auto with *.
    }
    
    intros apos.
    assert (forall i, 0 < alpha ^ i). intros i. apply pow_lt. auto.
    
    cut (prod (pow2 k) b <= alpha ^ pow2 k). {
      rewrite R.
      replace (pow2 k) with (n + (pow2 k - n))%nat at 2 by omega.
      rewrite pow_add.
      intros L.
      apply Rmult_le_reg_r in L; auto.
    }
    
    rewrite <-IH.
    pose proof mean_power_of_two b pb k as M.
    match type of M with ?a <= ?b => assert (0 <= a <= b) as M' end.
    { split; auto. apply sqrtk_pos, prod_pos, pb. }
    apply pow_incr with (n := pow2 k) in M'.
    rewrite pow2_sqrtk in M'. 2: apply prod_pos, pb.
    apply M'.
  
  - (* equality case *)
    intros E.
    pose proof mean_power_of_two_eq b pb k as HE.
    assert_specialize HE. {
      rewrite R, E, <-pow_add.
      replace (n + (pow2 k - n))%nat with (pow2 k) by omega.
      rewrite sqrtk_pow2; auto.
    }
    intros i li.
    specialize (HE i O).
    repeat assert_specialize HE by omega.
    exact_eq HE; f_equal; unfold b.
    + destruct (le_lt_dec n i). omega. auto.
    + destruct (le_lt_dec n 0). omega. auto.
Qed.
