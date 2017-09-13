Require Import Arith.
Require Import List.
Require Import Permutation.
Import ListNotations.

Definition normalize_direction : nat * nat -> nat * nat :=
  fun p => if fst p <=? snd p then p else (snd p, fst p).

Definition eulerian (E path : list (nat * nat)) :=
  Permutation
    (map normalize_direction E)
    (map normalize_direction path).

Inductive path : list (nat * nat) -> Prop :=
  | path_nil : path []
  | path_singleton x y : path [(x, y)]
  | path_cons x y z l :
      path ((y, z) :: l) ->
      path ((x, y) :: (y, z) :: l).

Fixpoint pathb l :=
  (match l with
  | [] => true
  | [(_, _)] => true
  | (x, y) :: (((y', z) :: _) as l) =>
    (y =? y') && pathb l
  end)%bool.

Lemma pathb_correct l : pathb l = true <-> path l.
Proof.
  induction l as [ | [x y] [ | [y' z] l] IHl ].
  - split; constructor.
  - split; constructor.
  - change (pathb ((x, y) :: (y', z) :: l))
    with ((y =? y') && pathb ((y', z) :: l))%bool.
    destruct (y =? y') eqn:E.
    + rewrite Bool.andb_true_l.
      rewrite IHl.
      apply Nat.eqb_eq in E. subst y'.
      split.
      * constructor; auto.
      * intros H; inversion H; auto.
    + simpl. split. discriminate.
      apply Nat.eqb_neq in E.
      intros H; inversion H; auto.
Qed.

Fixpoint pathbdir (swapfirst : bool) l :=
  (match l with
  | [] => true
  | [(_, _)] => true
  | (x, y) :: (((z, t) :: _) as l) =>
    let xy := if swapfirst then x else y in
    ((xy =? z) && pathbdir false l) ||
    ((xy =? t) && pathbdir true l)
  end)%bool.

Lemma pathbdir_rewrite first x y z t l :
  pathbdir first ((x, y) :: (z, t) :: l) =
  ((((if first then x else y) =? z) && pathbdir false ((z, t) :: l))
   || ((if first then x else y) =? t) && pathbdir true ((z, t) :: l))%bool.
Proof.
  reflexivity.
Qed.

Definition shouldswap p :=
  match p with
  | [] => true
  | (x, y) :: _ => negb (x <=? y)
  end.

Lemma pathbdir_correct p :
  pathb p = true ->
  pathbdir (shouldswap p) (map normalize_direction p) = true.
Proof.
  induction p as [ | [x y] [ | [y' z] l] IHl ].
  - intro. auto.
  - intro. simpl. unfold normalize_direction. simpl.
    destruct (x <=? y); auto.
  - change (pathb ((x, y) :: (y', z) :: l))
    with ((y =? y') && pathb ((y', z) :: l))%bool.
    destruct (y =? y') eqn:E. 2:discriminate.
    rewrite Bool.andb_true_l.
    intros HP.
    specialize (IHl HP).
    apply Nat.eqb_eq in E. subst y'.
    simpl (map _ _) in *.
    unfold normalize_direction at 1 2.
    unfold normalize_direction at 1 in IHl.
    simpl fst in *. simpl snd in *.
    simpl (shouldswap _) in *.
    destruct (y <=? z) eqn:Eyz, (x <=? y) eqn:Exy; simpl (negb _) in *.
    all: rewrite pathbdir_rewrite, IHl, Nat.eqb_refl.
    all: simpl (andb true true).
    all: auto.
    all: apply Bool.orb_true_r.
Qed.

Fixpoint remove1 {A} (eq_dec : forall x y, {x = y} + {x <> y}) (x : A) l : list A :=
  match l with
  | [] => []
  | y :: tl => if eq_dec x y then tl else y :: remove1 eq_dec x tl
  end.

Lemma permutation_remove1 {A} eq_dec (a : A) l l' :
  Permutation l l' ->
  Permutation (remove1 eq_dec a l) (remove1 eq_dec a l').
Proof.
  intros HP. induction HP as [| x p IHp | x y | l'' p1 p2 IHp1 IHp2].
  - constructor.
  - simpl. destruct (eq_dec _ _). auto. constructor. auto.
  - simpl. destruct (eq_dec _ x), (eq_dec _ y); subst; constructor.
    all: apply Permutation_refl.
  - econstructor; eauto.
Qed.

Lemma pe : forall x y : nat * nat, {x = y} + {x <> y}.
Proof.
  intros x y.
  decide equality; apply Nat.eq_dec.
Defined.

Fixpoint find x l :=
  match l with
    [] => False
  | y :: l => if pe x y then True else find x l
  end.

Lemma prune x l l' : Permutation (x :: l) l' -> find x l'.
Proof.
  intros P.
  assert (i : In x l'). apply Permutation_in with (x :: l). auto. left; auto.
  clear -i. induction l'. inversion i.
  simpl. simpl in i. destruct (pe x a). auto. apply IHl'. destruct i; auto.
  congruence.
Qed.

Lemma permutation_remove {A} eq_dec (a : A) l l' :
  Permutation (a :: l) l' ->
  Permutation l (remove1 eq_dec a l').
Proof.
  remember (a :: l) as al.
  intros HP. revert a l Heqal.
  induction HP; intros a L EL.
  - inversion EL.
  - inversion EL; subst. simpl. destruct (eq_dec a a). auto. tauto.
  - inversion EL; subst. simpl. destruct (eq_dec a _). subst. constructor.
    apply Permutation_refl. constructor.
    destruct (eq_dec a a). auto. tauto.
  - apply perm_trans with (remove1 eq_dec a l').
    apply (IHHP1 a L EL).
    apply permutation_remove1. auto.
Qed.

Theorem konigsberg_bridges :
  let E := [(0, 1); (0, 2); (0, 3); (1, 2); (1, 2); (2, 3); (2, 3)] in
  forall p, path p -> eulerian E p -> False.
Proof.
  intros E p Hpath Hperm.
  rewrite <-pathb_correct in Hpath.
  unfold eulerian in Hperm.
  replace (map normalize_direction E) with E in Hperm by reflexivity.
  apply pathbdir_correct in Hpath.
  revert Hperm Hpath.
  generalize (map normalize_direction p). intros l Hperm.
  generalize (shouldswap p).
  cut (pathbdir true l || pathbdir false l = false)%bool.
  { intros H b Hpath. destruct b; rewrite Hpath in H. discriminate.
    destruct (pathbdir true l); discriminate. }
  clear p.
  revert l Hperm.
  intros l Pl.
  
  assert (Hlen : length E = length l).
  { apply Permutation_length; auto. }
  
  assert (HE : forall x, In x l -> x = (0, 1) \/ x = (0, 2) \/ x = (0, 3) \/ x = (1, 2) \/ x = (2, 3)). {
    intros x i. apply Permutation_in with (l' := E) in i. 2:apply Permutation_sym, Pl.
    simpl in i.
    repeat (destruct i as [ <- | i ]; try tauto).
  }
  
  destruct l as [ | p0 l ]. inversion Hlen.
  destruct l as [ | p1 l ]. inversion Hlen.
  destruct l as [ | p2 l ]. inversion Hlen.
  destruct l as [ | p3 l ]. inversion Hlen.
  destruct l as [ | p4 l ]. inversion Hlen.
  destruct l as [ | p5 l ]. inversion Hlen.
  destruct l as [ | p6 l ]. inversion Hlen.
  destruct l as [ | ]. 2: inversion Hlen.
  clear Hlen.
  
  apply Permutation_sym in Pl.
  pose proof permutation_remove pe _ _ _ Pl as Pl1.
  pose proof permutation_remove pe _ _ _ Pl1 as Pl2.
  pose proof permutation_remove pe _ _ _ Pl2 as Pl3.
  pose proof permutation_remove pe _ _ _ Pl3 as Pl4.
  pose proof permutation_remove pe _ _ _ Pl4 as Pl5.
  pose proof permutation_remove pe _ _ _ Pl5 as Pl6.
  
  apply prune in Pl1.
  apply prune in Pl2.
  apply prune in Pl3.
  apply prune in Pl4.
  apply prune in Pl5.
  apply prune in Pl6.
  
  pose proof HE p0 ltac:(do 0 right; left; reflexivity) as E0.
  pose proof HE p1 ltac:(do 1 right; left; reflexivity) as E1.
  pose proof HE p2 ltac:(do 2 right; left; reflexivity) as E2.
  pose proof HE p3 ltac:(do 3 right; left; reflexivity) as E3.
  pose proof HE p4 ltac:(do 4 right; left; reflexivity) as E4.
  pose proof HE p5 ltac:(do 5 right; left; reflexivity) as E5.
  pose proof HE p6 ltac:(do 6 right; left; reflexivity) as E6.
  
  Ltac d H := destruct H as [ -> | [ -> | [ -> | [ -> | -> ]]]].
  Ltac t E P := d E; try reflexivity; try inversion P.
  
  d E0.
  all: t E1 Pl1.
  all: t E2 Pl2.
  all: t E3 Pl3.
  all: t E4 Pl4.
  all: t E5 Pl5.
  all: t E6 Pl6.
Qed.
