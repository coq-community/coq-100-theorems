Require Import Arith.

Definition sum f := fix s n := match n with O => f O | S x => f n + s x end.

Theorem arith_sum : forall a b n, 2 * sum (fun i => a + i * b) n = S n * (2 * a + n * b).
Proof.
intros a b n.
induction n; simpl; ring_simplify; auto.
rewrite IHn; ring.
Qed.
