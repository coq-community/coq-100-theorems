(* 1) La tactique inversion *)

(* On définit inductivement le prédicat binaire
"être strictement inférieur" de la façon suivante : *)
Inductive lt : nat -> nat -> Prop :=
  | lt_n : forall n, lt n (S n)
  | lt_S : forall n m, lt n m -> lt n (S m).

Notation "a < b" := (lt a b).

(* Pour savoir à quoi renvoie une notation, utilisez [Locate "sym".].
Et pour rappel, la tactique [unfold qualid.] permet de déplier
la définition de qualid. *)

Lemma not_lt_n_0 : forall n, ~ (n < 0).
Proof.
intros n H. inversion H.
Qed. (* efficace ! *)

(* Reprouvez ce lemme sans utiliser inversion (ou ses variantes). *)
Lemma dissected_not_lt_n_0 : forall n, ~ (n < 0).
Proof.
assert (forall n m, n < m -> m = 0 -> False).
intros n m Hnm Hm0.
destruct Hnm;
discriminate Hm0.
intros n Hn0.
apply (H n 0).
exact Hn0.
reflexivity.
Qed.

(* Prouvez que cette définition inductive permet de prouver les
deux axiomes de l'autre définition usuelle du prédicat lt. *)
Lemma lt_0_S_n : forall n, 0 < S n.
induction n; [apply lt_n | apply lt_S; exact IHn].
Qed.

Lemma lt_stable_by_S : forall n m, n < m -> S n < S m.
intros.
induction H.
apply lt_n.
apply lt_S.
exact IHlt.
Qed.

(* Donnez une preuve des deux résultats suivants : *)
Lemma lt_0_n : forall n, 0 < n * 2 -> 0 < n.
destruct n.
simpl; intro H; exact H.
intros _.
apply lt_0_S_n.
Qed.

Lemma lt_n_2n : forall n, 0 < n -> n < n * 2.
destruct n.
trivial.
induction n.
intros _.
simpl.
apply lt_n.
intros _.
assert (Hps : forall p, S p * 2 = S (S (p*2))).
  trivial.
rewrite (Hps (S n)).
apply lt_stable_by_S.
apply lt_S.
apply IHn.
apply lt_0_S_n.
Qed.



(* 2) Soupçon d'arithmétique *)

Lemma add_simpl : forall n m p, n + m = n + p -> m = p.
induction n.
trivial.
simpl.
intros.
injection H.
apply IHn.
Qed.


Lemma plus_neutral_r : forall a, a+0=a.
induction a; [ | simpl; rewrite IHa]; reflexivity.
Qed.

Lemma plus_comm : forall a b, a+b = b+a.
induction a.
intros b; rewrite plus_neutral_r; reflexivity.
simpl.
intros b; rewrite IHa.
induction b; [ | simpl; rewrite IHb]; reflexivity.
Qed.

Lemma mult_absorbing_r : forall a, a*0=0.
induction a; [ | simpl; exact IHa]; reflexivity.
Qed.

Lemma plus_assoc : forall a b c, a+(b+c)=a+b+c.
induction a; [ | simpl; intros; rewrite <- IHa]; reflexivity.
Qed.

Lemma mult_comm : forall a b, a*b = b*a.
induction a.
intros b; rewrite mult_absorbing_r; reflexivity.
simpl.
intros b; rewrite IHa.
induction b.
reflexivity.
simpl; rewrite <- IHb.
do 2 rewrite plus_assoc; rewrite (plus_comm a b).
reflexivity.
Qed.

Lemma plus_nul : forall a b, a+b = 0 -> a = 0.
destruct b.
intros.
rewrite <- H.
rewrite (plus_comm a 0).
trivial.
rewrite (plus_comm a (S b)).
simpl.
intro H. inversion H.
Qed.

Lemma mult_inj : forall b a, a*(S b) = 0 -> a=0.
intros b a.
rewrite (mult_comm a (S b)).
simpl.
intros.
apply (plus_nul a (b*a)).
exact H.
Qed.

Lemma pair_nat_ind_exo : forall (P : nat -> nat -> Prop), 
(forall n, P n O) -> (forall m, P O m) -> 
(forall n m, P n m -> P (S n) (S m)) -> forall n m, P n m. 
induction n.
intros. destruct m. apply H. apply H0.
induction m.
apply H.
apply H1.
apply IHn.
Qed.


Lemma mult_simpl : forall n m p, 0 < n -> m * n = p * n -> m = p.
intros n m p.
apply (pair_nat_ind_exo
  (fun m p => forall n, 0 < n -> m * n = p * n -> m = p)).

intros n0 n1 H H0.
induction n1.
  inversion H.
  apply (mult_inj n1 n0).
  rewrite H0.
  reflexivity.

intros n0 n1 H H0.
induction n1.
  inversion H.
  symmetry.
  apply (mult_inj n1 n0).
  rewrite <- H0.
  reflexivity.

clear n m p.
intros m p H n Hn0 Hmp.
cut (m=p). intro Hfac. rewrite Hfac. reflexivity.
apply (H n).
exact Hn0.

assert (plussune : forall a, S a * n = n + a * n).
  simpl.
  reflexivity.

assert (Hmp' :  n + m*n = n + p*n).
  rewrite <- (plussune m).
  rewrite <- (plussune p).
  exact Hmp.

apply (add_simpl n).
exact Hmp'.

Qed.



(* 3) Parité *)

Definition odd : nat -> Prop :=
   fun n:nat => exists n', n = 1 + n' * 2.

(* Une autre syntaxe est possible ! *)
Definition even (n : nat) : Prop :=
   exists n', n = n' * 2.

(* Donnez une définition inductive du prédicat "être pair". *)
Inductive even' : nat -> Prop :=
  | even'_O : even' 0
  | even'_S : forall n, even' n -> even' (S (S n))
.

(* Prouvez l'équivalence entre les deux définitions. *)
Lemma even_to' : forall n, even n -> even' n.
intros n H.
elim H.
clear H.
intro x.
generalize dependent n.
induction x.
intros n H. rewrite H.
apply even'_O.

intros n Hnx.
rewrite Hnx.
simpl.
apply even'_S.
apply (IHx (x * 2)).
reflexivity.
Qed.

Lemma even_from' : forall n, even' n -> even n.
Proof.
intros.
induction H.
exists 0;reflexivity.
destruct IHeven'.
exists (S x).
simpl.
rewrite <- H0.
reflexivity.
Qed.

(* Démontrez ensuite les propriétés suivantes. *)
Theorem even_succ_odd: forall n, even (S n) -> odd n.
intros n H.
destruct H.
destruct x.
inversion H.
exists x.
inversion H.
reflexivity.
Qed.

Theorem odd_succ_even : forall n, odd (S n) -> even n.
intros n H.
destruct H.
destruct x.
inversion H.
exists 0; reflexivity.
inversion H.
exists (S x).
reflexivity.
Qed.


Theorem not_odd_and_even: forall n, ~(odd n /\ even n).
induction n as [ | n IH].
intros [ [x H] _]. inversion H.
intros [H1 H2].
apply IH; split.
  apply even_succ_odd. apply H2. 
  apply odd_succ_even. apply H1. 
Qed. 

(* Une vieille version QUI MARCHE : 
intros n H.
destruct H.
destruct n.
inversion H.
inversion H1.
assert (odd n). apply even_succ_odd; exact H0.

destruct H.
destruct H0.
destruct H1.
generalize dependent H1.
generalize dependent x1.
generalize dependent H0.
generalize dependent x0.
generalize dependent  H.
generalize dependent  x.
generalize dependent  n.
induction n.
intros.
inversion H1.

intros xos oddssn xes evenssn xo oddsn.

destruct xos.
  inversion oddssn.

assert (oddssn_ : exists xos', S (S n) = 1 + S xos' * 2).
  exists xos.
  exact oddssn.
  destruct oddssn_.
  generalize dependent H.
  generalize dependent x.
  intros xos' oddssn_.

assert (evensn' : S n = S xos' * 2).
  assert (S (S n) = S (S xos' * 2)).
    rewrite oddssn_; reflexivity.
  inversion H.
  reflexivity.

destruct xos.
  inversion oddssn.
    destruct xo.
      inversion oddsn.
      rewrite H0 in H1.
      inversion H1.
    rewrite H0 in oddsn.
    inversion oddsn.

assert (oddn' : n = 1 + S xos * 2).
  assert(S n = S (S xos) * 2).
    injection oddssn.
    intro Hrev; rewrite Hrev; reflexivity.
  assert(S n = S (1 + (S xos) * 2)).
    rewrite H; reflexivity.
  injection H0.
    intro Hrev; rewrite Hrev; reflexivity.  


apply (IHn
  xo oddsn
  (S xos') evensn'
  (S xos) oddn'
).
Qed.*)

Theorem odd_or_even: forall n, odd n \/ even n.
induction n.
right; exists 0; reflexivity.
destruct IHn;
  [right | left];
  destruct H;
  [exists (x+1) | exists x];
  rewrite H;
  [rewrite (plus_comm x 1) | ];
  simpl;
  reflexivity.
Qed.

Lemma mult_plus_distr_l : forall a b c, a*(b+c) = a*b+a*c.
induction a.
reflexivity.
simpl.
intros; rewrite IHa.
do 2 rewrite <- plus_assoc.
cut (c + (a * b + a * c) = a * b + (c + a * c)).
  intros Hs; rewrite Hs; reflexivity.
do 2 rewrite plus_assoc.
rewrite (plus_comm c).
apply (add_simpl b); reflexivity.
Qed.

Lemma mult_1_l : forall n : nat, 1 * n = n.
simpl; apply plus_neutral_r.
Qed.

Lemma mult_plus_distr_r : forall a b c, (b+c)*a = b*a+c*a.
intros; do 3 rewrite <- (mult_comm a).
apply mult_plus_distr_l.
Qed.

Lemma mult_assoc : forall a b c : nat, a * (b * c) = a * b * c.
induction a; [ | simpl;intros; rewrite mult_plus_distr_r;rewrite IHa]; reflexivity.
Qed.

Theorem odd_square: forall n, odd n -> odd (n*n).
intros n On.
elim On.
intros x Hxn.
rewrite Hxn.
rewrite mult_plus_distr_r.
rewrite mult_1_l.
rewrite <- plus_assoc.
assert (assoc1 : forall a b, a + a*b = a*(1+b)).
  intros.
  rewrite (mult_comm a (1+b)).
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  rewrite mult_comm.
  reflexivity.
rewrite (assoc1 (x*2)).
rewrite (mult_comm x 2).
rewrite <- (mult_assoc).
rewrite mult_comm.
exists (x * (1 + (1 + 2 * x))).
reflexivity.
Qed.

(* Pénible, n'est-ce pas ?
La tactique [ring.] permet de résoudre une égalité entre polynômes
d'un anneau. Elle normalise chaque côté de l'égalité (par [ring_simplify])
puis vérifie l'égalité syntaxique entre les deux (par [reflexivity]).
Heureusement, ça marche aussi pour les semi-anneaux et pour l'utiliser
dans le cas des entiers naturels, il faut faire : *)
Require Import ArithRing.

(* Une tactique qui peut également servir est [replace T1 with T2 by tac.]
qui remplace les occurences de T1 par T2 si la tactique tac permet de
prouver T1 = T2. Si l'égalité est coriace, utilisez [replace T1 with T2.]. *)


(* 5) Irrationalité de sqrt(2) *)

(* Dans la suite, nous allons montrer qu'il n'existe pas d'entiers p et q
tels que q soit positif et p² = 2 * q² en suivant la preuve classique :
a) si p² est pair, p aussi ;
b) si p est pair, 4 divise p² donc 2 divise q² donc q est pair ;
c) donc il existe p' et q' plus petits vérifiant les mêmes propriétés ;
d) on conclue par l'absurde en supposant q minimal. *)

(* a *)
Theorem square_even: forall n, even (n*n) ->  even n.
intros n En2.
assert (odd n \/ even n).
  apply odd_or_even.
destruct H.
assert (odd (n * n)).
  apply odd_square; exact H.
apply False_ind.
elim (not_odd_and_even (n*n)).
split; [exact H0 | exact En2].
exact H.
Qed.

Lemma even_p : forall p q, p*p = q*q * 2 -> even p.
intros p q H.
assert (even (p*p)).
  exists (q*q); exact H.
apply square_even.
exact H0.
Qed.

(* b *)
Theorem even_q : forall p q, p*p = q*q*2 -> even q.
intros p q H.
assert (even p).
  apply (even_p p q H).
destruct H0.
assert (q * q = x * x * 2).
  elim (mult_simpl 2 (q*q) (x*x*2)).
  reflexivity.
  apply lt_S; apply lt_n.
  rewrite <- H.
  rewrite H0.
  ring.
elim (square_even q).
  intro x0; exists x0; exact H2.
exists (x*x).
exact H1.
Qed.

(* c *)
Theorem sqrt2_decr : forall p q, 0 < q ->
  p*p = q*q*2 -> exists p', exists q', 0 < q' /\ p'*p' = q'*q'*2 /\ q' < q.
intros p q Hqpos Hpq.
elim (even_p p q Hpq); intros p' Hp.
elim (even_q p q Hpq); intros q' Hq.
exists p'; exists q'.
split.
apply lt_0_n; rewrite <- Hq; exact Hqpos.
split.
assert (p' * p' * 2 * 2 = q' * q' * 2 * 2 * 2).
  assert (Rpp : p' * p' * 2 * 2 = p * p).
    rewrite Hp; ring.
  assert (Rqq : q' * q' * 2 * 2 = q * q).
    rewrite Hq; ring.
  rewrite Rpp.
  rewrite Rqq.
  exact Hpq.
apply (mult_simpl 2).
  apply lt_S; apply lt_n.
apply (mult_simpl 2).
  apply lt_S; apply lt_n.
exact H.
rewrite Hq; apply lt_n_2n; apply lt_0_n; rewrite <- Hq; exact Hqpos.
Qed.

Lemma lt_t : forall a b c, a < b -> b < c -> a < c.
intros a b c Hab Hbc.
induction Hbc;
  apply lt_S;
  [ | apply IHHbc];
  assumption.
Qed.

Lemma lt_bad : forall a b, a < S b -> a = b \/ a < b.
  intros a b H.
  inversion H; subst; auto.
Qed.  

(*Lemma lt_antistable_by_S : forall a b, S a < S b -> a < b.
induction a.
intros b Hsb.
destruct b.
  apply False_ind.  
  inversion Hsb.
  inversion H1.
apply lt_0_S_n.

intros b ssasb.

Lemma lt_st : forall a b c, a < b -> b < S c -> a < c.
intros a b c Hab Hbc.
induction Hbc.
Focus 2.
  apply lt_S;
  [ | apply IHHbc];
  assumption.
Qed.*)

(* d *)
(* Le raisonnement caché derrière "on conclut en supposant machin
minimal" correspond moralement à ce qu'on nomme la récurrence
forte. *)
Theorem strong_ind : forall (P: nat -> Prop),
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n m, m < n -> P m.
intros P Hstrong.
induction n.
intros m m0.
apply False_ind.
  inversion m0.

intros m Hmn.

assert (m = n \/ m < n).
  apply lt_bad; apply Hmn.

elim H.
intro Emn.
  rewrite Emn.
  apply Hstrong.
  exact IHn.

apply IHn.

Qed.

Theorem sqrt2_not_rat_min : forall qmin q,
  q < qmin -> 0 < q -> forall p,  p*p <> q*q*2.
apply (strong_ind (fun q => (0 < q -> forall p,  p*p <> q*q*2))).
intros q SIH qpos p Hpq.
destruct (sqrt2_decr p q) as [p' [q' [q'pos [Hpq' qq']]]]; [exact qpos | exact Hpq | ].
apply (SIH q' qq' q'pos p' Hpq').
Qed.

Theorem sqrt2_not_rational : forall p q, q <> 0 -> p*p <> q*q*2.
intros p q qnn.
assert (qpos : 0 < q).
 destruct q.
  apply (False_ind _ (qnn (refl_equal 0))).
  exact (lt_0_S_n q).
apply (sqrt2_not_rat_min (S q) q); [apply lt_n | exact qpos].
Qed.

