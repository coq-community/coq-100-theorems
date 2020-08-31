(*
MIT License

Copyright (c) 2017 Frédéric Chardard, Institut Camille Jordan /
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


(*
This file contains:
_A construction of a nth-root of complex numbers.
_A construction of a cubic root on C such that if the argument is real, then the result is also real.
_A proof that Cardan-Tartaglia formula solves the general cubic equation in the field of complex numbers.

This file was checked by Coq without error with following configuration:

base-bigarray             base  Bigarray library distributed with the OCaml comp
base-num                  base  Num library distributed with the OCaml compiler
base-threads              base  Threads library distributed with the OCaml compi
base-unix                 base  Unix library distributed with the OCaml compiler
camlp5                    7.03  Preprocessor-pretty-printer of OCaml
conf-gtksourceview           2  Virtual package relying on a GtkSourceView syste
conf-m4                      1  Virtual package relying on m4
coq                      8.7.0  Formal proof management system.
coq-coquelicot           3.0.1  A Coq formalization of real analysis compatible 
coq-mathcomp-ssreflect   1.6.2  Small Scale Reflection
coqide                   8.7.0  IDE of the Coq formal proof management system.
depext                   1.0.5  Query and install external dependencies of OPAM 
lablgtk                 2.18.5  OCaml interface to GTK+
num                          0  The Num library for arbitrary-precision integer 
ocamlfind                1.7.3  A library manager for OCaml

OPAM 1.2.2 on
Linux version 4.4.0-96-generic (buildd@lgw01-10) (gcc version 5.4.0 20160609 (Ubuntu 5.4.0-6ubuntu1~16.04.4) ) #119-Ubuntu SMP Tue Sep 12 14:59:54 UTC 2017

*)
Require Import Reals Coq.Reals.Rtrigo_def Coquelicot.Coquelicot Coquelicot.ElemFct Fourier.



Open Scope R_scope.




Lemma Reqdec : forall x:R, {x=0} + {x<>0}.
intros.
pose (total_order_T x 0).
induction s.
 induction a.
   right.
   intro.
   rewrite H in a.
   apply (Rgt_irrefl _ a).
   left.
   assumption.
   right.
   intro.
   rewrite H in b.
   apply (Rgt_irrefl _ b).
Qed.

Definition rargument (x:R) (y:R) : R := if (Reqdec y) 
then if(Rcase_abs x) then  PI else 0
else 2*atan(y/(x+sqrt(x^2+y^2))).


Lemma normpos : forall x:R, forall y:R, 0<=x^2+y^2.
intros.
apply Rplus_le_le_0_compat;
apply pow2_ge_0.
Qed.


Lemma normspos : forall x:R, forall y:R, x<>0 -> 0<x^2+y^2.
intros.
apply Rplus_lt_le_0_compat.
 induction (Rcase_abs x).
  cutrewrite(x^2=(-x)^2).
   apply Rmult_lt_0_compat.
    apply Ropp_0_gt_lt_contravar.
   assumption.
  apply Rmult_lt_0_compat.
    apply Ropp_0_gt_lt_contravar.
   assumption.
   apply Rlt_0_1.
  field.
 assert(0<x).
  destruct b.
   assumption.
   exfalso.
   apply H.
  apply H0.

unfold pow.
rewrite Rmult_1_r.
apply Rmult_lt_0_compat;
assumption.
apply pow2_ge_0.
Qed.

Lemma cosneq0 : forall x:R, x<> PI/2 -> x<>-(PI/2) -> -PI < x -> x < PI -> cos(x)<>0.
intros.
induction (total_order_T (PI/2) x).
induction a.
apply Rlt_not_eq.
apply cos_lt_0.
fourier.
apply (Rlt_trans _ PI).
assumption.
cutrewrite(3*(PI/2)=PI+PI/2).
fourier.
field.
exfalso.
apply H.
rewrite b.
reflexivity.

induction (total_order_T (-(PI/2)) x).
induction a.
apply Rgt_not_eq.
apply cos_gt_0;
assumption.
exfalso.
apply H0.
rewrite b0.
reflexivity.

remember (x+PI) as y.
assert(x=y-PI).
rewrite Heqy.
field.
rewrite H3.
rewrite cos_minus.
rewrite cos_PI.
rewrite sin_PI.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
intro.
assert(cos(y)<>0).
apply Rgt_not_eq.

rewrite Heqy.
apply cos_gt_0.
apply Rminus_gt.
apply Rgt_minus in H1.
cutrewrite(x + PI - - (PI / 2)=(x - - PI) + (PI / 2)).
apply Rplus_lt_le_0_compat.
assumption.
apply Rle_div_r.
fourier.
fourier.
field.

apply Rgt_minus in b0.
apply Rminus_gt.
cutrewrite(PI / 2 - (x + PI)= - (PI / 2) - x ).
assumption.
field.
apply H5.
rewrite<-Ropp_involutive at 1.
rewrite<-Ropp_involutive.
apply Ropp_eq_compat.
rewrite Ropp_0.
rewrite<-H4.
field.
Qed.




Lemma cos2atan : forall x:R, x<> PI/2 -> x<>-(PI/2) -> -PI < x -> x < PI -> (cos(2*x))=2/(1+(tan x)^2)-1.
intros.
cutrewrite((tan(x))^2=(1-(cos(x))^2)/(cos(x))^2).
rewrite cos_2a.
cutrewrite(sin(x)*sin(x)=1-(cos(x))²).
unfold Rsqr.
field.

split.
apply cosneq0;
assumption.

intro.
cut(0<>1).
intro.
apply H4.
rewrite<-H3.
field.
fourier.
fold (Rsqr (sin x)).
rewrite sin2.
reflexivity.
cutrewrite( (cos(x))^2=(cos(x))²).
rewrite<-sin2.
unfold tan.
unfold Rsqr.
field.
apply cosneq0;
assumption.
unfold Rsqr.
field.
Qed.

Lemma coordnorm : forall x:R, forall y:R, y<>0 -> -x<sqrt(x^2+y^2).
intros.
induction(total_order_T 0 x).
induction a.
apply (Rlt_trans _ 0).
fourier.
apply sqrt_lt_R0.
apply normspos.
intro.

rewrite H0 in a.
apply (Rlt_irrefl _ a).
rewrite<-b.
rewrite Ropp_0.
unfold pow at 1.
rewrite Rmult_0_l.
rewrite Rplus_0_l.
apply sqrt_lt_R0.
unfold pow.
rewrite Rmult_1_r.
induction(total_order_T 0 y).
induction a.
apply Rmult_lt_0_compat;
assumption.
exfalso.
apply H.
rewrite b0.
reflexivity.
cutrewrite(y*y=(-y)*(-y)).
apply Rmult_lt_0_compat;
fourier.
field.
apply Rsqr_incrst_0.
rewrite Rsqr_sqrt.
rewrite<-Rsqr_neg.
unfold Rsqr.
unfold pow.
repeat rewrite Rmult_1_r.
rewrite<-Rplus_0_r at 1.
apply Rplus_lt_compat_l.
pose proof (normspos y 0 H).
unfold pow in H0.
repeat rewrite Rmult_1_r in H0.
rewrite Rmult_0_l in H0.
rewrite Rplus_0_r in H0.
assumption.
apply normpos.
fourier.
apply sqrt_pos.
Qed.


Lemma coordnormb : forall x:R, forall y:R, y<>0 -> 0<sqrt(x^2+y^2)+x.
intros.
pose proof coordnorm x y H.
apply Rgt_minus in H0.
cutrewrite(sqrt (x ^ 2 + y ^ 2) - - x= sqrt (x ^ 2 + y ^ 2)+x) in H0.
assumption.
field.
Qed.


Lemma cosarg : forall x:R, forall y:R, cos(rargument x y)*sqrt(x^2+y^2)=x.
intros.
unfold rargument.
induction (Reqdec y).
induction (Rcase_abs x).
rewrite a.
rewrite cos_PI.
unfold pow.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
rewrite Rmult_1_r.
rewrite<-Ropp_involutive at 1.
rewrite<-Ropp_involutive.
apply Ropp_eq_compat.
apply Rsqr_inj.
cutrewrite( - (-1 * sqrt (x * x))=sqrt(x*x)).
apply sqrt_pos.
field.
fourier.
rewrite Rsqr_pow2.
rewrite Rsqr_pow2.
cutrewrite(-x=sqrt(x*x)).
field.
cutrewrite(x*x=(-x)²).
rewrite sqrt_Rsqr.
reflexivity.
fourier.
unfold Rsqr.
field.
rewrite cos_0.
rewrite a.
unfold pow.
rewrite Rmult_0_l.
rewrite Rplus_0_r.
rewrite Rmult_1_r.
rewrite Rmult_1_l.
cutrewrite(x*x=x²).
rewrite sqrt_Rsqr.
reflexivity.
unfold Rsqr.

cutrewrite((-x)*(-x)=x*x).
fourier.
field.
unfold Rsqr.
reflexivity.
rewrite cos2atan.
remember (sqrt (x^2+y^2) ) as u.
rewrite atan_right_inv.
assert(u^2=x^2+y^2).
rewrite Hequ.
unfold pow.
repeat rewrite Rmult_1_r.
rewrite sqrt_sqrt.
reflexivity.
cutrewrite(x*x+y*y=x^2+y^2).
apply normpos.
field.

cutrewrite((2 / (1 + (y / (x + u)) ^ 2) - 1) * u=(u^2 + 2*u*x + x^2 - y^2)*u/(u^2 + 2*u*x + x^2+y^2)).
rewrite H at 1.
assert(x ^ 2 + y ^ 2 + 2 * u * x + x ^ 2 - y ^ 2=2*x*(u+x)).
field.
rewrite H0.
cutrewrite(u ^ 2 + 2 * u * x + x ^ 2 + y ^ 2=2*u^2+2*x*u).
field.
cutrewrite(2*u^2+2*x*u=2*u*(u+x)).
apply Rmult_integral_contrapositive.
split.
apply Rmult_integral_contrapositive.
split.
admit (* apply Qreals.IZR_nz. *).
rewrite Hequ.
rewrite<-sqrt_0.
intro.
apply sqrt_inj in H1.
pose proof normspos y x b.
cutrewrite(y^2+x^2=x^2+y^2) in H2.
rewrite H1 in H2.
apply (Rlt_irrefl 0).
assumption.
field.
apply normpos.
info_auto with *.

pose proof coordnormb x y b.
rewrite<-Hequ in H1.
apply Rgt_not_eq.
apply Rlt_gt.
assumption.
field.
rewrite H.
field.
field.
split.
cutrewrite(u ^ 2 + 2 * u * x + x ^ 2 + y ^ 2 =2*u^2+2*u*x).
cutrewrite(2 * u ^ 2 + 2 * u * x=2*u*(x+u)).
apply Rmult_integral_contrapositive.
split.
apply Rmult_integral_contrapositive.
split.
admit. (* apply Qreals.IZR_nz. *)
rewrite Hequ.
apply Rgt_not_eq.
apply sqrt_lt_R0.
pose proof normspos y x b.
cutrewrite(x^2+y^2=y^2+x^2).
assumption.
field.
apply Rgt_not_eq.
rewrite Rplus_comm.
rewrite Hequ.
apply coordnormb.
assumption.
field.
rewrite H.
field.
apply Rgt_not_eq.
rewrite Rplus_comm.
rewrite Hequ.
apply coordnormb.
assumption.
apply Rlt_not_eq.
apply atan_bound.
apply Rgt_not_eq.
apply Rlt_gt.
cutrewrite(-(PI/2)=-PI/2).
apply atan_bound.
field.
apply(Rlt_trans _ (-PI/2)).
apply Rminus_gt.
assert (-PI/2--PI=PI/2).
field.
rewrite H.
apply PI2_RGT_0.
apply atan_bound.
apply(Rlt_trans _ (PI/2)).
apply atan_bound.
apply Rminus_gt.
assert (PI-PI/2=PI/2).
field.
rewrite H.
apply PI2_RGT_0.
Admitted.

Lemma sinarg : forall x:R, forall y:R, sin(rargument x y)*sqrt(x^2+y^2)=y.
assert(forall u:R, forall v:R, forall w:R, ((0<=u /\ 0<=w) \/ (u<=0 /\ w<=0)) -> 0<=v -> u²*v²=w² -> u*v=w).
intros.
destruct H.
destruct H.
apply Rsqr_inj.
apply Rmult_le_pos.
assumption.
assumption.
assumption.
rewrite<-H1.
unfold Rsqr.
field.
destruct H.
rewrite<-Ropp_involutive.
rewrite<-Ropp_involutive at 1.
apply Ropp_eq_compat.
apply Rsqr_inj.
apply Ropp_0_ge_le_contravar.
apply Rle_ge.
apply Rmult_le_0_r;
assumption.
apply Ropp_0_ge_le_contravar.
apply Rle_ge.
assumption.
rewrite<-(Rsqr_neg w).
rewrite<-H1.
unfold Rsqr.
field.
intros.
apply H.
induction (Rcase_abs y).
right.
split.
unfold rargument.
induction (Reqdec y).
fourier.
left.
rewrite<-Ropp_involutive at 1.
apply Ropp_0_lt_gt_contravar.
rewrite<-sin_neg.
apply sin_gt_0.
rewrite Ropp_mult_distr_r.
apply Rmult_lt_0_compat.
fourier.
rewrite<-atan_opp.
rewrite<-atan_0.
apply atan_increasing.
rewrite<-Ropp_div.
apply Rdiv_lt_0_compat.
fourier.
cutrewrite(x + sqrt (x ^ 2 + y ^ 2)=sqrt (x ^ 2 + y ^ 2)+x).
apply coordnormb.
assumption.
field.
rewrite<-(Ropp_involutive PI).
apply Ropp_lt_contravar.
cut(forall z:R,-PI<2*atan(z)).
intro.
apply H0.
intro.
apply (Rmult_gt_reg_l (/2)).
fourier.
cutrewrite(/ 2 * (2 * atan z)=atan z).
cutrewrite(/ 2 * - PI=-PI/2).
apply atan_bound.
field.
field.
fourier.
left.
split.
unfold rargument.
induction (Reqdec y).
induction (Rcase_abs x).
rewrite sin_PI.
fourier.
rewrite sin_0.
fourier.
left.
apply sin_gt_0.
apply Rmult_lt_0_compat.
fourier.
rewrite<-atan_0.
apply atan_increasing.
apply Rdiv_lt_0_compat.
destruct b.
assumption.
exfalso.
apply (b0 H0).
cutrewrite(x + sqrt (x ^ 2 + y ^ 2)=sqrt (x ^ 2 + y ^ 2)+x).
apply coordnormb.
assumption.
field.
cut(forall z:R,2*atan(z)<PI).
intro.
apply H0.
intro.
apply (Rmult_lt_reg_r (/2)).
fourier.
cutrewrite((2 * atan z)*/2=atan z).
cutrewrite(PI*/2=PI/2).
apply atan_bound.
field.
field.
fourier.
apply sqrt_pos.
rewrite sin2.
assert(forall u v w:R, v²-(u*v)²=w² ->(1-u²)*v²=w²).
intros.
rewrite<-H0.
unfold Rsqr.
field.
apply H0.
rewrite cosarg.
rewrite Rsqr_sqrt.
unfold Rsqr.
field.
apply normpos.
Qed.

Definition cargument (z:C) : R:=rargument (Re z) (Im z).



Fixpoint pow (r : C) (n : nat) {struct n} : C := match n with
                                            | 0%nat => 1
                                            | S n0 => (r * pow r n0)%C
                                            end.


Theorem moivre : forall n:nat, forall x:R, pow (cos x,sin x) n=(cos ((INR n)*x), sin ((INR n)*x))%C.
induction n.
unfold pow.
unfold INR.
intros.
rewrite (Rmult_0_l x).
rewrite cos_0.
rewrite sin_0.
reflexivity.
intro.
rewrite S_INR.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite cos_plus.
rewrite sin_plus.
unfold pow.
fold pow.
rewrite IHn.
unfold Cmult.
unfold fst.
unfold snd.
f_equal;
unfold fst;
unfold snd;
field.
Qed.


Theorem powexp : forall n:nat, forall x:R, (exp(x))^n=exp((INR n)*x).
induction n.
unfold INR.
intro.
rewrite Rmult_0_l.
rewrite exp_0.
rewrite pow_O.
reflexivity.
intros.
rewrite<-tech_pow_Rmult.
rewrite S_INR.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite exp_plus.
rewrite IHn.
field.
Qed.

Theorem compow: forall n : nat, forall z:C, forall u:C, (pow (z*u)%C n)=((pow z n)*(pow u n))%C.
induction n.
intros.
unfold pow.
unfold RtoC.
unfold Cmult.
unfold fst.
unfold snd.
f_equal;
unfold fst;
unfold snd;
field.
intros.
unfold pow.
fold pow.
rewrite IHn.
field.
Qed.

Lemma trigoform : forall z:C, z=((cos( rargument (Re z)(Im z)),sin( rargument (Re z)(Im z)))%C*(sqrt((Re z)^2+(Im z)^2),0)%C)%C.
intro.
unfold Cmult.
unfold fst.
unfold snd.
rewrite Rmult_0_r.
rewrite Rmult_0_r.
rewrite cosarg.
rewrite sinarg.
unfold Re.
unfold Im.
induction z.
f_equal;
unfold fst;
unfold snd;
field.
Qed.

Lemma RCpow : forall n:nat,forall x:R, pow (x,0)%C n = (x^n,0)%C.
induction n.
intro.
unfold pow.
rewrite pow_O.
reflexivity.
intro.
rewrite<-tech_pow_Rmult.
unfold pow at 1.
fold pow.
rewrite IHn.
unfold RtoC.
unfold Cmult.
f_equal;
unfold fst;
unfold snd;
field.
Qed.


Open Scope C_scope.

Definition nroot (n:nat) (z:C) : C:= 
if Ceq_dec z 0 then 0 
else (cos((cargument z)/(INR n)),sin((cargument z)/(INR n)))*((exp((ln (sqrt((Re z)^2+(Im z)^2)))/(INR n))),0).

Theorem identification_argument : forall A:Type, forall f:R->A,forall x y:R,x=y->f(x)=f(y).
intros.
rewrite H.
reflexivity.
Qed.

Theorem nroot_pown : forall n:nat,forall z:C,n<>O-> pow (nroot n z) n=z.
pose proof (identification_argument R) as HHH.
intros.
unfold nroot.
induction (Ceq_dec z 0).
rewrite a.
unfold pow.
induction n.
exfalso.
apply H.
reflexivity.
apply Cmult_0_l.
rewrite compow.
rewrite moivre.
rewrite (RCpow n).
rewrite powexp.
rewrite (trigoform z) at 5.
assert(forall a b c d:C, a=b -> c=d -> a*c=b*d).
intros.
rewrite H0.
rewrite H1.
reflexivity.
apply H0.
unfold cargument.
f_equal;
unfold fst;
unfold snd;
apply HHH;
field.
info_auto with *.
info_auto with *.

f_equal.
unfold fst.
rewrite<-exp_ln.
apply HHH.
field.
auto with *.
apply sqrt_lt_R0.
induction z.
unfold Re.
unfold Im.
unfold fst.
unfold snd.
induction (Reqdec a).
induction (Reqdec b0).
exfalso.
apply b.
rewrite a0.
rewrite a1.
reflexivity.
rewrite Rplus_comm.
apply normspos.
assumption.
apply normspos.
assumption.
Qed.

Definition cubicroot (z:C) := if(Rcase_abs (Re z)) then -nroot 3 (-z) else nroot 3 z.

Lemma cubicroot3 : forall z:C, pow (cubicroot z) 3=z.
intro.
unfold cubicroot.
induction (Rcase_abs (Re z)).
transitivity (-pow (nroot 3 (-z)) 3).
unfold pow.
field.
rewrite nroot_pown.
field.
discriminate.
apply nroot_pown.
discriminate.
Qed.

Lemma cubicrootreal : forall (x:R), 0%R=Im (cubicroot x).
intro.
unfold cubicroot.
induction  (Rcase_abs (Re x)).
unfold nroot.
unfold cargument.
unfold rargument.

unfold Im.
unfold Re.
induction (Ceq_dec (-x) 0).
unfold Copp.
unfold RtoC.
unfold snd.
field.
unfold Cmult.
unfold Copp at 1.
unfold snd at 1.
induction(Reqdec (snd (- x)%C)).
unfold snd at 1.
rewrite a0.
unfold  RtoC.
unfold Copp.
unfold fst.
induction(Rcase_abs (- x)).
unfold RtoC in a.
unfold Re in a.
unfold fst in a.
fourier.
unfold snd.
unfold Rdiv.
rewrite Rmult_0_l.
rewrite Rmult_0_r.
rewrite sin_0.
rewrite Rmult_0_l.
field.
unfold RtoC.
unfold Copp.

unfold snd.
unfold Rdiv.
unfold fst.
rewrite Ropp_0.
rewrite Rmult_0_l.
rewrite Rmult_0_r.
rewrite atan_0.
rewrite Rmult_0_r.
rewrite Rmult_0_l.

rewrite sin_0.
rewrite Rmult_0_l.
field.
unfold RtoC in b.
unfold Re in b.
unfold fst in b.



unfold nroot.
unfold cargument.
unfold rargument.

unfold Im.
unfold Re.
induction (Ceq_dec (x) 0).
unfold RtoC.
unfold snd.
reflexivity.
unfold RtoC.
unfold fst.
induction(Reqdec (snd (x,0))).
induction(Rcase_abs x).
fourier.
unfold Cmult.
unfold snd.
unfold Rdiv.
rewrite Rmult_0_r.
rewrite Rmult_0_l.
rewrite sin_0.
rewrite Rmult_0_l.
field.
unfold snd in b1.
exfalso.
apply b1.
reflexivity.
Qed.

Definition CJ := ((-1/2)%R,((sqrt 3)/2)%R)%C.

Lemma CJ3 : pow CJ 3=1%C.
assert(CJ=(cos(2*(PI/3))%R,sin(2*(PI/3))%R)).
unfold CJ.

rewrite cos_2PI3.
rewrite sin_2PI3.
reflexivity.
rewrite H.
rewrite moivre.
unfold RtoC.
rewrite<-cos_2PI.
rewrite<-sin_2PI.
apply (identification_argument _ (fun X:R => (cos X,sin X)%C )).
unfold INR.
field.
Qed.

Lemma CJ2: pow CJ 2=-CJ-1.
unfold pow.
unfold CJ.
unfold Cmult.
unfold RtoC.
unfold Copp.
unfold Cminus.
unfold Copp.
unfold Cplus.
unfold fst.
unfold snd.
repeat rewrite Rmult_0_r.
repeat rewrite Rmult_0_l.
repeat rewrite Rplus_0_l.
repeat rewrite Rplus_0_r.
repeat rewrite Rminus_0_l.
repeat rewrite Rminus_0_r.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
unfold Rminus.
cutrewrite((sqrt 3 / 2 * (sqrt 3 / 2))%R=(3/4)%R).
f_equal;
unfold fst;
unfold snd;
field.
cutrewrite((sqrt 3 / 2 * (sqrt 3 / 2)%R)%R=((sqrt 3*sqrt 3)%R/(2*2)%R)%R).
rewrite sqrt_sqrt.
field.
fourier.
field.
Qed.

Lemma factorisationdeg3 : forall z1 z2 z3:C, forall z:C, 
(z-z1)*(z-z2)*(z-z3)=pow z 3+(-(z1+z2+z3))*pow z 2+(z1*z2+z2*z3+z3*z1)*z+(-(z1*z2*z3)).
intros.
unfold pow.
rewrite (Cmult_1_r z).
field.
Qed.


Lemma shiftdeg3 : forall u:C, forall a b c:C, forall z:C, 
pow (z+u) 3+a*pow (z+u) 2+b*(z+u)+c
=pow z 3+(a+3*u)*pow z 2+(b+2*u*a+3*pow u 2)*z+(c+b*u+a*pow u 2+pow u 3).
intros.
unfold pow.
cutrewrite(RtoC 3=(1+1+1)).
cutrewrite(RtoC 2=1+1).
repeat rewrite Cmult_plus_distr_l.
repeat rewrite Cmult_plus_distr_r.
repeat rewrite (Cmult_1_r).
repeat rewrite (Cmult_1_l).
field.
unfold RtoC,Cplus,fst,snd.
f_equal;
field.
unfold RtoC,Cplus,fst,snd.
f_equal;
field.

Qed.


Lemma integernonzero : forall n:nat, n<>0%nat -> RtoC (INR n)<>0.
induction n.
intro.
exfalso.
apply H.
reflexivity.
intro.
intro.
assert(fst (INR (S n),0) = INR (S n)).
unfold fst.
reflexivity.
unfold RtoC in H0.
rewrite H0 in H1.
unfold fst in H1.
cutrewrite (0=INR 0) in H1.
apply INR_eq in H1.
apply H.
rewrite H1.
reflexivity.
unfold INR.
reflexivity.
Qed.


(*


  |- ~(a = Cx(&0))
     ==> let p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2)
         and q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
                 (Cx(&54) * a pow 3) in
         let s = csqrt(q pow 2 + p pow 3) in
         let s1 = if p = Cx(&0) then ccbrt(Cx(&2) * q) else ccbrt(q + s) in
         let s2 = --s1 * (Cx(&1) + ii * csqrt(Cx(&3))) / Cx(&2)
         and s3 = --s1 * (Cx(&1) - ii * csqrt(Cx(&3))) / Cx(&2) in
         if p = Cx(&0) then
           a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
              x = s1 - b / (Cx(&3) * a) \/
              x = s2 - b / (Cx(&3) * a) \/
              x = s3 - b / (Cx(&3) * a)
         else
           ~(s1 = Cx(&0)) /\
           (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
               x = s1 - p / s1 - b / (Cx(&3) * a) \/
               x = s2 - p / s2 - b / (Cx(&3) * a) \/
               x = s3 - p / s3 - b / (Cx(&3) * a))


 *)



Theorem Cardan_Tartaglia : forall a1 a2 a3 :C,
    let s := -a1 / 3 in 
    let p := a2 + 2 * s * a1 + 3 * pow s 2 in
    let q := a3 + a2 * s + a1 * pow s 2 + pow s 3 in
    (p <> 0 ->
     let Delta := pow (q / 2) 2 + pow (p / 3) 3 in
     let alpha := cubicroot (- (q / 2) + nroot 2 Delta) in
     let beta := - (p / 3) / alpha in
     let z1 := alpha + beta in
     let z2 := alpha * CJ + beta * pow CJ 2 in
     let z3 := alpha * pow CJ 2 + beta * CJ in
     forall u : C,
       (u - (s + z1)) * (u - (s + z2)) * (u - (s + z3))
       = pow u 3 + a1 * pow u 2 + a2 * u + a3)
    /\
    (p = 0 ->
     let z1 := - cubicroot q in
     let z2 := z1 * CJ in
     let z3 := z1 * pow CJ 2 in
     forall u : C,
       (u - (s + z1)) * (u - (s + z2)) * (u - (s + z3))
       = pow u 3 + a1 * pow u 2 + a2 * u + a3).

assert(RtoC 1<>RtoC 0) as neq0_1.
unfold RtoC.
intro.
assert(fst (1,0) =1).
unfold fst.
reflexivity.
rewrite H in H0.
unfold fst in H0.
fourier.

assert(RtoC 2<>RtoC 0) as neq0_2.
unfold RtoC.
intro.
assert(fst (2,0) =2).
unfold fst.
reflexivity.
rewrite H in H0.
unfold fst in H0.
fourier.


assert(RtoC 3<>RtoC 0) as neq0_3.
intro.
unfold RtoC in H.
assert(fst (3,0) =3).
unfold fst.
reflexivity.
rewrite H in H0.
unfold fst in H0.
fourier.


assert(forall z0:C, z0<>0 -> /z0 <> 0) as invnot0.
intros.
assert(z0 * / z0<>0).
rewrite Cinv_r.
assumption.
assumption.
intro.
apply H0.
rewrite H1.
rewrite Cmult_0_r.
reflexivity.



intros.
split.

intros.
assert(alpha<>0) as alphaneq0.
assert(pow alpha 3<>0) as alpha3.

unfold alpha.
rewrite cubicroot3.
assert(forall a b:C, pow a 2<>pow b 2 -> -a+b<>0 ).
intros.
intro.
apply H0.
replace a with b.
reflexivity.
rewrite <-(Cplus_0_r a).
rewrite<-H1.
field.
apply H0.
rewrite nroot_pown.
unfold Delta.
assert(forall a b c:C, a=b->c<>0->a<>b+c).
intros.
intro.
apply H2.
rewrite H1 in H3.
rewrite<-(Cplus_opp_r b).
rewrite H3 at 1.
field.
apply H1.
unfold pow.
repeat rewrite Cmult_1_r.
field.
assumption.
unfold pow.
repeat rewrite Cmult_1_r.
unfold Cdiv.
repeat apply Cmult_neq_0;
try apply invnot0;
try assumption.


discriminate.
intro.
apply alpha3.
rewrite H0.
unfold pow.
apply Cmult_0_l.

pose (z:=u-s).
assert(u=z+s) as Hszu.
unfold z.
field.
rewrite Hszu.
rewrite (shiftdeg3 s).
fold p.
fold q.
unfold s at 7.
rewrite (Cmult_comm 3).
unfold Cdiv.
rewrite<-(Cmult_assoc _ _ 3).
rewrite (Cinv_l _ neq0_3).
rewrite (Cmult_1_r).
rewrite Cplus_opp_r.
rewrite (Cmult_0_l).
rewrite (Cplus_0_r).
assert(forall f g h:C, f+g-(g+h)=f-h) as mincancel.
intros.
field.
repeat rewrite mincancel.


rewrite factorisationdeg3.
assert(z1+z2+z3=0).
unfold z1,z2,z3.
rewrite CJ2.
field.
rewrite H0.
rewrite Copp_0.
rewrite Cmult_0_l.
rewrite Cplus_0_r.
assert(z1 * z2 + z2 * z3 + z3 * z1=p) as coeffp.
unfold z1,z2,z3.
repeat rewrite Cmult_plus_distr_l.
repeat rewrite Cmult_plus_distr_r.
repeat rewrite Cmult_plus_distr_l.
repeat rewrite Cmult_plus_distr_r.
cutrewrite( (alpha * CJ * (alpha * pow CJ 2) + beta * pow CJ 2 * (alpha * pow CJ 2) +
 (alpha * CJ * (beta * CJ) + beta * pow CJ 2 * (beta * CJ)))
=(alpha * alpha *(CJ * pow CJ 2) + beta  * alpha * ( pow CJ 2  * pow CJ 2) +
 (alpha * beta * (CJ * CJ) + beta * beta * (CJ * pow CJ 2)))).
cutrewrite(CJ*pow CJ 2=1).
cutrewrite(CJ*CJ=-CJ-1).
cutrewrite((pow CJ 2)*(pow CJ 2)=CJ).
rewrite CJ2.
cutrewrite(p=-(1+1+1)*alpha*beta).
field.
unfold beta.
cutrewrite( (1+1+1)=3).
field.
split.

assumption.
assumption.
unfold RtoC.
unfold Cplus.
unfold fst.
unfold snd.
f_equal.
field.
field.

unfold pow.
assert(CJ=(pow CJ 3)*CJ) as CJ4.
rewrite CJ3.
rewrite Cmult_1_l.
reflexivity.
rewrite CJ4 at 5.
unfold pow.
rewrite Cmult_1_r.
field.
symmetry.
etransitivity.
symmetry.
apply CJ2.
unfold pow.
rewrite Cmult_1_r.
reflexivity.
etransitivity.
Focus 2.
apply CJ3.
unfold pow.
reflexivity.
field.
rewrite coeffp.
assert(q=- (z1 * z2 * z3)) as coeffq.
unfold z1,z2,z3.

cutrewrite(q=-(CJ*(pow CJ 2)*alpha*alpha*alpha
+CJ*(pow CJ 2)*beta*beta*beta
+(CJ*CJ+(pow CJ 2)*(pow CJ 2)+CJ*(pow CJ 2))*alpha*alpha*beta
+(CJ*(pow CJ 2)+CJ*CJ+(pow CJ 2)*(pow CJ 2))*alpha*beta*beta)).
field.
cutrewrite(CJ*pow CJ 2=1).
cutrewrite(CJ * CJ=-CJ-1).
cutrewrite(pow CJ 2 * pow CJ 2=CJ).
cutrewrite(q=-(pow alpha 3+pow beta 3)).
unfold pow.
field.
cutrewrite(pow beta 3=(-pow (p/3) 3)/(pow alpha 3)).
unfold alpha at 1.
rewrite cubicroot3.

repeat rewrite Copp_plus_distr.
transitivity(--(q/2)+q/2).
unfold RtoC.
unfold Cdiv.
unfold Cinv.
unfold Cmult.
unfold Cminus.
unfold Copp.
unfold Cplus.
induction q.
f_equal;
unfold fst;
unfold snd;
field.

rewrite<-Cplus_assoc.
f_equal.

field_simplify.
unfold alpha at 1.
rewrite cubicroot3.
rewrite Cmult_plus_distr_l.

assert(forall a :C,-a*a=-pow a 2).
intros.
unfold pow.
rewrite Cmult_1_r.
field.

rewrite H1.
rewrite nroot_pown.
unfold Delta at 2.
unfold alpha.
rewrite cubicroot3.
unfold pow.
repeat rewrite Cmult_1_r.
remember (q/2) as qhalf.
field.
split.
assumption.

rewrite<-cubicroot3 at 1.
fold alpha.
unfold pow.
rewrite Cmult_1_r.
repeat apply Cmult_neq_0;
assumption.

discriminate.

unfold pow.
rewrite Cmult_1_r.
repeat apply Cmult_neq_0;
assumption.

assumption.

unfold pow.
unfold beta.
repeat rewrite Cmult_1_r.
field.
split;
assumption.

transitivity ((pow CJ 3)*CJ).
unfold pow.
repeat rewrite Cmult_1_r.
field.
rewrite CJ3.
rewrite Cmult_1_l.
reflexivity.

transitivity(pow CJ 2).
unfold pow.
repeat rewrite Cmult_1_r.
reflexivity.
apply CJ2.

etransitivity.
Focus 2.
apply CJ3.
unfold pow.
reflexivity.

rewrite<-coeffq.
reflexivity.

intros.


pose (z:=u-s).
assert(u=z+s) as Hszu.
unfold z.
field.
rewrite Hszu.
rewrite (shiftdeg3 s).
fold p.
fold q.
unfold s at 7.
rewrite (Cmult_comm 3).
unfold Cdiv.
rewrite<-(Cmult_assoc _ _ 3).
rewrite (Cinv_l _ neq0_3).
rewrite (Cmult_1_r).
rewrite Cplus_opp_r.
repeat rewrite (Cmult_0_l).
repeat rewrite (Cplus_0_r).
assert(forall f g h:C, f+g-(g+h)=f-h) as mincancel.
intros.
field.
repeat rewrite mincancel.
rewrite factorisationdeg3.
f_equal.
f_equal.
unfold z3,z2.
rewrite CJ2.
field.
rewrite H.
unfold z3,z2.
rewrite CJ2 at 1.
rewrite Cmult_0_l.
unfold pow.
field.
rewrite<-(Cmult_1_r q).
rewrite<-(cubicroot3 q).
rewrite<-CJ3.
unfold z3,z2,z1,pow.
field.
Qed.

(* Print Assumptions Cardan_Tartaglia. *)

