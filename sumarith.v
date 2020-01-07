Require Import Arith.

Definition sum f := fix s n := match n with O => f O | S x => f n + s x end.

Theorem arith_sum : forall a b n, 2 * sum (fun i => a + i * b) n = S n * (2 * a + n * b).
Proof.
intros a b n.
induction n; simpl; ring_simplify; auto.
try change (BinNat.N.to_nat 2) with 2.
try change (BinNat.N.to_nat 3) with 3.
try change (BinNat.N.to_nat 4) with 4.
rewrite IHn; ring.
Qed.
