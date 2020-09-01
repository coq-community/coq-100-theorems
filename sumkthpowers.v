(*
MIT License

Copyright (c) 2020 Frédéric Chardard, Institut Camille Jordan /
Université Jean Monnet de Saint-Etienne

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

Require Import Reals.
Open Scope R_scope.


Fixpoint bernoullicoeff (n:nat) (k:nat) : R:=
match n with |  O  => match k with | O => INR 1
                                   | _ => INR 0
                      end
             |(S m)=> 
  match k with 
| O    => (sum_f_R0 (fun l => -((bernoullicoeff m l)*(/INR (S l))*(INR n)*/ INR (S (S l)) )) m)
| (S l)=> (bernoullicoeff m l)*/(INR (S l))*(INR n)
  end
end.


Definition bernoulli_polynomial (n:nat) (x:R):=
(sum_f_R0 (fun l => (bernoullicoeff n l) *x^l) n).


Theorem bernoulli_polynomial_derivable_pt_lim:
forall n:nat,forall x:R,
derivable_pt_lim (bernoulli_polynomial (S n)) x ((bernoulli_polynomial n x)*(INR (S n))).
  intros.
  erewrite (_:(_*(INR (S n))=_)).
 apply derivable_pt_lim_fs.
 apply Nat.lt_0_succ.
 Unshelve.
 unfold Init.Nat.pred.
 rewrite Rmult_comm at 1.
unfold bernoullicoeff.
fold bernoullicoeff.
unfold bernoulli_polynomial.
rewrite scal_sum.
apply sum_eq.
intros.
repeat rewrite<-Rmult_assoc.
field.
apply not_0_INR.
discriminate.
Qed.

Theorem bernoulli_polynomial_derivable_pt_lim_shift:
forall n:nat,forall x:R,
    derivable_pt_lim (fun x=> (bernoulli_polynomial (S n) (x+1))) x ((bernoulli_polynomial n (x+1))*(INR (S n))).
  unfold derivable_pt_lim.
  intros.
destruct (bernoulli_polynomial_derivable_pt_lim n (x+1) eps) as [delta der].
assumption.
exists delta.
intros.
enough(x+h+1=x+1+h) as ->.
apply der;
assumption.
field.
Qed.


Lemma sumzero : forall n:nat, sum_f_R0 (fun _ => 0:R) n=(0:R).
induction n.
simpl sum_f_R0.
reflexivity.
simpl.
rewrite IHn.
apply Rplus_0_r.
Qed.

Theorem bernoulli_polynomial_val_0_1:
  forall n:nat,n<>1%nat  -> bernoulli_polynomial n 0=bernoulli_polynomial n 1.
  intros n nneq1.
  unfold bernoulli_polynomial.
  transitivity ((bernoullicoeff n 0)+0).
destruct n.
unfold sum_f_R0.
field.

rewrite decomp_sum.
unfold Init.Nat.pred.
 rewrite pow_O.
rewrite Rmult_1_r.
f_equal.


rewrite<-(sumzero n) at 1.
apply sum_eq.
intros.
simpl pow.
field.
apply Nat.lt_0_succ.

destruct n.
unfold sum_f_R0,bernoullicoeff.
field.

rewrite decomp_sum.
unfold Init.Nat.pred.
rewrite pow_O.
rewrite Rmult_1_r.
f_equal.
destruct n.
exfalso.
apply nneq1.
reflexivity.
rewrite decomp_sum.
rewrite pow1.
rewrite Rmult_1_r.
simpl Init.Nat.pred.
unfold bernoullicoeff.
fold bernoullicoeff.

unfold bernoullicoeff at 1.
fold bernoullicoeff.
rewrite Rmult_comm.
rewrite<-Rmult_assoc.
rewrite scal_sum.
rewrite Rmult_comm.
rewrite scal_sum.

rewrite<-sum_plus.
rewrite<-(sumzero n) at 1.
apply sum_eq.
intros.
rewrite pow1.
simpl(INR 1).
field.
split;
  apply not_0_INR;
  discriminate.
apply (neq_0_lt).
discriminate.
apply (neq_0_lt).
discriminate.
Qed.



Lemma primitive_diff : forall f g fp : (R->R), 
(forall x:R, derivable_pt_lim f x (fp x))->
(forall x:R, derivable_pt_lim g x (fp x))->
forall x:R, f x=(plus_fct g (fct_cte ((f 0)-(g 0)))) x.
intros f g fp fder gder.
assert(forall x:R, derivable_pt_lim (f-g) x ((fun _ => 0) x)) as fmpder.
intro x.
rewrite<-(Rminus_diag_eq _ _ (eq_refl (fp x))).
apply derivable_pt_lim_minus.
apply fder.
apply gder.
intro x.
unfold plus_fct,fct_cte.
assert((f-g)%F x=(f-g)%F 0) as diffeq.
destruct (total_order_T x 0) as [xneg|xin];
try destruct xneg as [xin|x0];
try (rewrite x0;
     reflexivity);
pose proof (MVT_cor2 (f-g)%F (fun _ => 0) _ _ xin (fun x _ => fmpder x)) as mvt;
destruct mvt as [c mvt];
destruct mvt as [mvt ineq];
rewrite Rmult_0_l in mvt;
pose proof (Rminus_diag_uniq _ _ mvt) as eqfi;
rewrite eqfi;
reflexivity.
unfold minus_fct in diffeq.
rewrite<-diffeq.
field.
Qed.

Lemma primitive_eq:forall f g fp : (R->R), 
(forall x:R, derivable_pt_lim f x (fp x))->
(forall x:R, derivable_pt_lim g x (fp x))->
f 0=g 0->
forall x:R, f x=g x.
intros f g fp fder gder init x.
transitivity ((plus_fct g (fct_cte ((f 0)-(g 0)))) x).
rewrite (primitive_diff f g fp);
try assumption;
try reflexivity.
unfold plus_fct,fct_cte.
rewrite init.
field.
Qed.

Lemma kthpowers : forall n:nat, forall x:R,
x^n*(INR (S n))=(bernoulli_polynomial (S n) (x+1))-(bernoulli_polynomial (S n) x).
induction n.
intro.
unfold bernoulli_polynomial,sum_f_R0,bernoullicoeff.
unfold sum_f_R0,INR,pow.
field.

apply (primitive_eq _ _ (fun x=>(INR (S n))*x^n*(INR (S (S n)))) ).
intro x.
apply (derivable_pt_lim_scal_right (fun x=>x^(S n)) x _ (INR (S (S n)))).
pose proof (derivable_pt_lim_pow x (S n)) as derpow.
unfold Init.Nat.pred in derpow.
apply derpow.
intro x.
erewrite(_:(INR (S n) * x ^ n * INR (S (S n)))=_).
apply derivable_pt_lim_minus.
apply bernoulli_polynomial_derivable_pt_lim_shift.
apply bernoulli_polynomial_derivable_pt_lim.
unfold pow.
repeat rewrite Rmult_0_l.
rewrite bernoulli_polynomial_val_0_1.
rewrite Rplus_0_l.
rewrite Rminus_diag_eq;
reflexivity.
discriminate.
Unshelve.
rewrite(Rmult_comm (INR (S n))).
rewrite IHn.
field.
Qed.

Lemma sum_kthpowers : forall r:nat, forall n:nat, 
(0<r)%nat->
sum_f_R0 (fun k => ((INR k)^r)%R) n
=((bernoulli_polynomial (S r) (INR n+1))-(bernoulli_polynomial (S r) 0))/(INR r+1).
intros r n rneq0.
induction n.
unfold INR.
fold INR.
rewrite bernoulli_polynomial_val_0_1.
rewrite Rplus_0_l.
unfold sum_f_R0.
unfold pow,INR.
fold INR.
fold pow.
induction r.
exfalso.
apply (lt_0_neq 0).
assumption.
reflexivity.
unfold pow.
fold pow.
field.
rewrite<-S_INR.
apply not_0_INR.
discriminate.
apply not_eq_S.
intro.
apply (lt_0_neq _ rneq0).
symmetry.
assumption.

unfold sum_f_R0.
fold sum_f_R0.
rewrite IHn.
enough(INR (S n) ^ r=(INR (S n) ^r * (INR (S r)))/(INR (S r))) as ->.
rewrite kthpowers.
repeat rewrite<-S_INR.
field.
apply not_0_INR.
discriminate.
field.
apply not_0_INR.
discriminate.
Qed.
