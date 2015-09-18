Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

Fixpoint sumdigits n (f : nat -> Z) :=
  match n with
  | O => f O
  | S n => f (S n) + sumdigits n f
  end.

Fixpoint number n (f : nat -> Z) :=
  match n with
  | O => f O
  | S n => f (S n) + 10 * number n f
  end.

Theorem div3 : forall n d,
  (number n d) mod 3 = (sumdigits n d) mod 3.
Proof.
  intros n d; induction n.
    auto.
    
    change ((d (S n) + 10 * number n d) mod 3 = (d (S n) + sumdigits n d) mod 3).
    rewrite Zplus_mod, Zmult_mod, IHn.
    remember (sumdigits n d) as SU.
    replace (10 mod 3) with 1 by trivial.
    rewrite Zmult_1_l, Zmod_mod.
    rewrite <- Zplus_mod.
    reflexivity.
Qed.







