Require Import Omega.

Theorem pigeonhole :
  forall m n, m < n -> forall f, (forall i, f i < m) ->
    { i : nat & { j : nat | i < j < n /\ f i = f j } }.
Proof.
  (* It is enough to prove the special case when [n = 1 + m] *)
  cut (forall n f, (forall i, f i < n) ->  { i : _ & ((i < S n) * { j | j < i /\ f i = f j })%type }).
    intros; destruct (H (n-1) f) as [i [Li [j [Lj Hij]]]]; eauto. intros i; specialize (H1 i); omega.
    exists j, i; intuition.
  
  (* We do an induction on n (the base cases, for 1 and 2, are easy) *)
  destruct n. intros f L; specialize (L 0); exfalso; inversion L.
  induction n; intros f B. now pose proof conj (B 0) (B 1); exists 1; intuition; exists 0; intuition.
  
  (* We can know if there is some [i] such that [f i = k] if we restrict the search space. *)
  Lemma bounded_lookup f (k:nat) m : {i | i < m /\ f i = k} + ~ exists i, i < m /\ f i = k.
  Proof.
    induction m. now right; intros [i [L _]]; inversion L.
    destruct IHm as [[i Hi]|N]. now left; exists i; omega.
    assert (D:{f m = k} + {f m <> k}) by eauto with *. destruct D. now subst; eauto.
    right; intros [i Hi]. assert (D:i = m \/ i < m) by omega; intuition eauto. now subst; eauto.
  Defined.
  
  (* If, for some i, [f i = f m] then it is easy: *)
  destruct (bounded_lookup f (f (S (S n))) (S (S n))) as [[i Hi]|J].
    now exists (S (S n)); intuition; eauto.
  
  (* Otherwise to apply the induction, we build a function g from f "stripped" from [f m] *)
  assert (Eg: { g : nat -> nat |
    (forall a, a < S (S n) -> f a < f (S (S n)) -> g a = f a) /\
    (forall a, a < S (S n) -> f a > f (S (S n)) -> g a = f a - 1) /\
    (forall a, g a < S n)}).
    set (g := fun a => if lt_dec a (S (S n))
      then if lt_dec (f a) (f (S (S n))) then f a else f a - 1
      else 0); exists g.
    split; [|split]; intro a; intros; unfold g;
    destruct (lt_dec a (S (S n))); destruct (lt_dec (f a) (f (S (S n)))); omega || auto.
      now specialize (B (S (S n))); omega.
      now specialize (B a); omega.
  destruct Eg as [g [g1 [g2 g3]]].
  
  (* We can now apply the induction on g which get us a collision for g: *)
  destruct (IHn g) as [i [Li [j [Lj E]]]]. now intros a; eauto.
  
  (* Finally we get, from the collision on g, a collision on f: *)
  exists i; intuition eauto; exists j; intuition eauto.
  assert (D: forall a, f a = f (S (S n)) \/ f a < f (S (S n)) \/  f a > f (S (S n))) by (intro;omega).
  assert (j < S (S n)) by omega.
  destruct (D i), (D j); intuition eauto; try solve [exfalso; eapply J; eauto].
    rewrite (g1 i) in E; eauto. now rewrite (g1 j) in E; eauto.
    rewrite (g1 i) in E; eauto. rewrite (g2 j) in E; eauto. omega.
    rewrite (g2 i) in E; eauto. rewrite (g1 j) in E; eauto. omega.
    rewrite (g2 i) in E; eauto. rewrite (g2 j) in E; eauto. omega.
Defined.

(* underlying functional *)
Definition find m n (L:m < n) f (H:forall i, f i < m) :=
  let p := pigeonhole m n L f H in (projT1 p, projT1 (projT2 p)).
