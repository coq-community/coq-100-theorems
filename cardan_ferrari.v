(*
MIT License

Copyright (c) 2017-2020 Frédéric Chardard, Institut Camille Jordan /
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
_A construction of a cubic root on C such that if the argument is real, 
then the result is also real.
_A proof that Cardan-Tartaglia formula solves the general cubic equation 
in the field of complex numbers.
__A proof that Ferrari method solves the general quartic equation in the 
field of complex numbers.


This file was checked by Coq without error with following configuration:
base-bigarray          base
base-threads           base
base-unix              base
cairo2                 0.6.1       Binding to Cairo, a 2D Vector Graphics Library
conf-cairo             1           Virtual package relying on a Cairo system installation
conf-findutils         1           Virtual package relying on findutils
conf-g++               1.0         Virtual package relying on the g++ compiler (for C++)
conf-gnome-icon-theme3 0           Virtual package relying on gnome-icon-theme
conf-gtk3              18          Virtual package relying on GTK+ 3
conf-gtksourceview3    0+2         Virtual package relying on a GtkSourceView-3 system installation
conf-m4                1           Virtual package relying on m4
conf-pkg-config        1.3         Virtual package relying on pkg-config installation
coq                    8.12.0      Formal proof management system
coq-coquelicot         3.1.0       A Coq formalization of real analysis compatible with the standard library
coq-mathcomp-ssreflect 1.11.0      Small Scale Reflection
coqide                 8.12.0      IDE of the Coq formal proof management system
dune                   2.7.0       Fast, portable, and opinionated build system
dune-configurator      2.7.0       Helper library for gathering system configuration
lablgtk3               3.1.1       OCaml interface to GTK+3
lablgtk3-sourceview3   3.1.1       OCaml interface to GTK+ gtksourceview library
num                    1.3         The legacy Num library for arbitrary-precision integer and rational arithmetic
ocaml                  4.08.1      The OCaml compiler (virtual package)
ocaml-config           1           OCaml Switch Configuration
ocaml-system           4.08.1      The OCaml compiler (system version, from outside of opam)
ocamlfind              1.8.1       A library manager for OCaml

on Linux empmeticj012 5.4.0-42-generic #46-Ubuntu SMP Fri Jul 10 00:24:02 UTC 2020 x86_64 x86_64 x86_64 GNU/Linux
(Ubuntu 20.04.1 LTS)
with OPAM 2.0.5.
*)

Require Import Reals Coq.Reals.Rtrigo_def Coquelicot.Coquelicot Coquelicot.ElemFct Lra.



Open Scope R_scope.

Ltac Rsimpl:=
repeat (
try rewrite Ropp_involutive;
try rewrite Ropp_0;
try rewrite Rplus_opp_l;
try rewrite Rplus_opp_r;
try rewrite Rplus_0_l;
try rewrite Rplus_0_r;
try rewrite Rmult_1_l;
try rewrite Rmult_1_r;
try rewrite Rmult_0_l;
try rewrite Rmult_0_r
).


Ltac Csimpl:=
  repeat (
      try rewrite Copp_0;
      try rewrite Cplus_opp_r;
      try rewrite Cplus_0_l;
      try rewrite Cplus_0_r;
      try rewrite Cmult_0_r;
      try rewrite Cmult_1_r;
      try rewrite Cmult_0_l;
      try rewrite Cmult_1_l).


Lemma contraposition_neg : forall P Q:Prop, ( P -> Q ) -> ( (~Q) -> (~P)).
intros P Q hyp negQ vP.
apply negQ.
apply hyp.
assumption.
Qed.

Lemma f_notequal : forall A B:Type,forall f : (A->B), forall x y :A, f x<>f y -> x<>y.
intros A B f x y.
apply contraposition_neg.
apply f_equal.
Qed.

Lemma Rlt_neq: forall x:R, forall y:R, x<y -> y<>x.
  intros x y ineq.
  apply not_eq_sym.
  apply Rlt_not_eq.
  assumption.
Qed.


Lemma Reqdec : forall x:R, {x=0} + {x<>0}.
intros.
induction (total_order_T x 0) as [xneg|xspos].
 induction xneg as [xsneg|x0].
   right.
   apply not_eq_sym.
   apply Rlt_neq.
   assumption.
   left.
   assumption.
   right.
   apply Rlt_neq.
   assumption.
Qed.


Lemma normpos : forall x:R, forall y:R, 0<=x^2+y^2.
  intros.
  apply Rplus_le_le_0_compat;
    apply pow2_ge_0.
Qed.

Lemma normspos : forall x:R, forall y:R, x<>0 -> 0<x^2+y^2.
intros.
do 2 rewrite<-Rsqr_pow2.
apply Rplus_lt_le_0_compat.
apply Rsqr_pos_lt.
assumption.
apply Rle_0_sqr.
Qed.

Lemma coordnorm : forall x:R, forall y:R, y<>0 -> -x<sqrt(x^2+y^2).
  intros.
  apply (Rle_lt_trans _ (Rabs x)).
  rewrite<-Rabs_Ropp.
  apply Rle_abs.
  rewrite<-sqrt_Rsqr_abs.
  apply sqrt_lt_1_alt.
  split.
  apply Rle_0_sqr.
  repeat rewrite<-Rsqr_pow2.
  apply Rminus_gt.
  unfold Rminus.
  rewrite Rplus_comm.
  rewrite<-Rplus_assoc.
  Rsimpl.
  apply Rlt_0_sqr.
  assumption.
Qed.



Lemma coordnormb : forall x:R, forall y:R, y<>0 -> 0<sqrt(x^2+y^2)+x.
  intros.
  rewrite<-(Ropp_involutive x) at 2.
  apply Rlt_Rminus.
  apply coordnorm.
  assumption.
Qed.



Ltac Cfequal:= 
repeat unfold RtoC,Cminus,Cplus,Copp,Cmult,Cdiv,Cinv,Re,Im,fst,snd.




Lemma cosatanspos : forall x:R, cos(atan x)>0.
intro.
apply cos_gt_0.
rewrite<-Ropp_div.
apply (proj1 (atan_bound _)).
apply (proj2 (atan_bound _)).
Qed.

Lemma cosatan : forall x:R, Rsqr (cos(atan x))=(/(1+Rsqr x))%R.
  intro.
  rewrite<-(atan_right_inv x) at 2.
  unfold tan.
  rewrite Rsqr_div.
  rewrite sin2.
  unfold Rsqr.
  field.
  split.
  apply (Rlt_neq _ _ (cosatanspos _)).
  unfold Rminus.
  rewrite Rplus_comm.
  rewrite Rplus_assoc.
  Rsimpl.
  apply R1_neq_R0.
  apply (Rlt_neq _ _ (cosatanspos _)).
Qed.




Open Scope C_scope.


Fixpoint Cpow (r : C) (n : nat) {struct n} : C := match n with
                                            | 0%nat => 1
                                            | S n0 => (r * Cpow r n0)%C
                                            end.


Theorem moivre : forall n:nat, forall x:R, 
    Cpow (cos x,sin x) n=(cos ((INR n)*x), sin ((INR n)*x))%C.
  induction n.
  unfold Cpow,INR.
  intros.
  Rsimpl.
  rewrite cos_0.
  rewrite sin_0.
  reflexivity.
  intro.
  rewrite S_INR.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  rewrite cos_plus.
  rewrite sin_plus.
  unfold Cpow.
  fold Cpow.
  rewrite IHn.
  Cfequal.
  f_equal;
    field.
Qed.


Definition Rneg_or_not : forall z:C, 
 {0<Re z} + {Im z<>0} +{Im z=0 /\ Re z<=0}.
intros.
destruct z as (u,v).
unfold Im,Re,fst,snd.
unfold Rle.
destruct (total_order_T u 0) as [uneg|uspos];
  try destruct uneg as [usneg|u0];
  destruct (Reqdec v) as [veq0|vneq0];
  auto.

Qed.


Definition Csqrt:=fun (z:C) =>
let (u,v):=z in
let a:=(sqrt(((Cmod z)+u)/2))%R in
let b:=(if (Rneg_or_not z) 
   then v/2/a
   else  sqrt(-u))%R in
(a,b)%C : C.


Lemma Csqrt_Cpow2 : forall z: C, (Csqrt z)*(Csqrt z)=z.
  intro.
  unfold Cmult.
  pose (fst (Csqrt z)) as u.
  pose (snd (Csqrt z)) as v.

  fold u.
  fold v.
  fold (Rsqr u).
  fold (Rsqr v).

induction z as (x,y).
rewrite Rmult_comm.
rewrite<-double.

unfold Csqrt,Re,Im,snd,fst in u,v.
fold u in v.

destruct Rneg_or_not as [znotneg|zneg].
unfold Im,Re,fst,snd in *.

assert(0<(Cmod(x,y)+x)%R) as nspos.
unfold Cmod,fst,snd.
destruct znotneg as [xspos|ynot0].
apply Rplus_le_lt_0_compat.
apply sqrt_pos.
assumption.
apply coordnormb.
assumption.

assert(0<u) as uspos.
unfold u.
apply sqrt_lt_R0.
apply Rdiv_lt_0_compat.
assumption.
apply Rlt_0_2.

pose proof (Rlt_neq _ _ uspos) as uneq0.

unfold v.
f_equal.
rewrite Rsqr_div.
rewrite<-(Rdiv_1 (Rsqr u)) at 1.
rewrite Rdiv_minus.
fold (Rsqr (Rsqr u)).
unfold u.
rewrite Rsqr_sqrt.
rewrite Rsqr_div.
rewrite Rsqr_plus.
unfold Cmod at 1.
unfold fst,snd.
rewrite Rsqr_sqrt.
unfold Rsqr.
field.
apply Rlt_neq.
assumption.
apply normpos.
apply Rlt_neq.
apply Rlt_0_2.

left.
apply Rdiv_lt_0_compat.
assumption.
apply Rlt_0_2.

apply R1_neq_R0.
apply Rlt_neq.
apply Rlt_0_sqr.
assumption.
assumption.

field.
assumption.


unfold Re,Im,fst,snd in *.
unfold u,v.
destruct zneg as [yeq0 xneg].
rewrite yeq0.
fold (RtoC x).
rewrite (Cmod_R x).
rewrite Rabs_left1.
unfold Rdiv.
Rsimpl.
rewrite sqrt_0.
Rsimpl.
rewrite Rsqr_sqrt.
unfold Rminus,Rsqr.
Rsimpl.
reflexivity.
rewrite<-Ropp_0.
apply Ropp_le_contravar.
assumption.
assumption.
Qed.



Definition cargument (z: C) : R := 
if (Rneg_or_not z) then (INR 2)*atan((Im (Csqrt z))/(Re (Csqrt z))) 
else PI.

Lemma trigoform: forall z : C,
                   z=(cos(cargument z),sin(cargument z))*(Cmod z,0).
  intro.
  unfold cargument.
  induction Rneg_or_not as [znotneg|zneg].

  pose proof (Csqrt_Cpow2 z) as z2.
  induction (Csqrt z) as (u,v).

  assert (Cmod z<>0%R) as zmodnot0.
  intro mz0.
  pose proof (Cmod_eq_0 z mz0) as z0.
  rewrite z0 in znotneg.
  unfold Re,Im,fst,snd,RtoC in znotneg.
  destruct znotneg as [rezspos|imzneq0].
  apply (Rlt_neq _ _ rezspos).
  reflexivity.
  apply imzneq0.
  reflexivity.

  assert(u<>0) as uneq0.
  intro ueq0.
  rewrite ueq0 in z2.
  unfold Cmult,fst,snd in z2.
  repeat rewrite Rmult_0_r in z2.
  repeat rewrite Rmult_0_l in z2.
  unfold Rminus in z2.
  repeat rewrite Rplus_0_l in z2.
  rewrite<-z2 in znotneg.
  unfold Re,Im,fst,snd in znotneg.
  destruct znotneg as [sqrneg|neq00].
  apply (Rlt_not_ge (Rsqr v) 0).
  unfold Rsqr.
  apply Ropp_lt_cancel.
  rewrite Ropp_0.
  assumption.
  apply Rle_ge.
  apply Rle_0_sqr.
  apply neq00.
  reflexivity.

  assert( forall x:R, (x*x)%R =(Rsqr x)%R) as multsqr.
  unfold Rsqr.
  reflexivity.


  rewrite<-z2.
  unfold Im,Re,fst,snd.
  rewrite z2 at 2.

  unfold Cmult,Re,Im,fst,snd.
  Rsimpl.
  rewrite cos_2a.

  repeat rewrite multsqr.
  rewrite sin2.

  
  assert( forall x:R, cos(x)<>0 -> (sin((INR 2) * x))%R =(2*(tan x)*(Rsqr (cos x)))%R) as sineq.
  intros.
  unfold tan,Rsqr.
  rewrite sin_2a.
  field.
  assumption.
  rewrite sineq.
  rewrite cosatan.
  rewrite atan_right_inv.
  

  assert(Cmod z=(u*u+v*v)%R) as modz.
  rewrite<-z2.
  rewrite Cmod_mult.
  repeat rewrite multsqr.
  unfold Cmod,fst,snd.
  rewrite Rsqr_sqrt.
  repeat rewrite Rsqr_pow2.
  reflexivity.
  apply normpos.

  rewrite modz.
  unfold Rsqr.
  rewrite modz in zmodnot0.
  f_equal;
    field;
    split;
    assumption.

  apply Rlt_neq.
  apply cosatanspos.


  rewrite cos_PI.
  rewrite sin_PI.
  unfold Cmult,fst,snd.
  destruct z as (u,v).
  unfold Im,snd,Re,fst,Rminus in zneg.
  rewrite (proj1 zneg).
  fold (RtoC u).
  rewrite Cmod_R.
  unfold Rminus,RtoC.
  Rsimpl.
  rewrite Rabs_left1.
  f_equal.
    field.
  apply (proj2 zneg).
Qed.
 
Lemma factorisationdeg3 : forall z1 z2 z3:C, forall z:C, 
(z-z1)*(z-z2)*(z-z3)=Cpow z 3+(-(z1+z2+z3))*Cpow z 2+(z1*z2+z2*z3+z3*z1)*z+(-(z1*z2*z3)).
intros.
unfold Cpow.
field.
Qed.





Theorem Cpowexp : forall n:nat, forall x:R, ((exp(x))^n=exp((INR n)*x)) % R.
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

Theorem comCpow: forall n : nat, forall z:C, forall u:C, (Cpow (z*u)%C n)=((Cpow z n)*(Cpow u n))%C.
induction n.
intros.
unfold Cpow.
Cfequal.
f_equal;
field.
intros.
unfold Cpow.
fold Cpow.
rewrite IHn.
field.
Qed.


Lemma RCpow : forall n:nat,forall x:R, Cpow (x,0)%C n = ((x^n)%R,0)%C.
induction n.
intro.
unfold Cpow.
rewrite pow_O.
reflexivity.
intro.
rewrite<-tech_pow_Rmult.
unfold Cpow at 1.
fold Cpow.
rewrite IHn.
Cfequal.
unfold Rminus.
Rsimpl.
reflexivity.
Qed.



Definition nroot (n:nat) (z:C) : C:= 
if Ceq_dec z 0 then  0 
else let argn:=((cargument z)/(INR n))%R in
  (cos(argn),sin(argn))*(exp((ln (Cmod z))/(INR n)),0).


Theorem nroot_Cpown : forall n:nat,forall z:C,n<>O-> Cpow (nroot n z) n=z.
intros n z nneq0.
unfold nroot.
induction (Ceq_dec z 0) as [zeq0|zneq0].
rewrite zeq0.
unfold Cpow.
induction n.
contradiction nneq0.
reflexivity.
apply Cmult_0_l.
rewrite comCpow.
rewrite moivre.
rewrite (RCpow n).
rewrite Cpowexp.
rewrite (trigoform z) at 4.
unfold Rdiv.
repeat rewrite<-Rmult_assoc.
repeat rewrite Rinv_r_simpl_m.
rewrite exp_ln.
reflexivity.
apply Cmod_gt_0.
assumption.
apply not_0_INR.
assumption.
apply not_0_INR.
assumption.
Qed.

Lemma nrootpositive : forall x:R, forall n:nat, 0<=x -> Im( nroot n x ) =0%R.
intros.
unfold nroot.
induction(Ceq_dec x 0) as [xeq0|xneq0].
unfold RtoC,Im,snd.
reflexivity.

unfold Im,Re,Cmult,fst,snd.
Rsimpl.
apply Rmult_eq_0_compat_r.
rewrite<-sin_0.
f_equal.
unfold Rdiv.
apply Rmult_eq_0_compat_r.
unfold cargument,Csqrt.
rewrite Cmod_R.
unfold Rabs,Re,Im,RtoC,fst,snd.
destruct Rcase_abs as [xneg|xpos].
lra.
unfold Rdiv.
rewrite<-double.
unfold Rdiv.

destruct Rneg_or_not as [vra|fal].
repeat rewrite Rmult_0_l.
rewrite atan_0.
apply Rmult_0_r.

exfalso.
unfold Re,Im,fst,snd in fal.
destruct fal.
apply xneq0.
f_equal.
apply Rle_antisym;
assumption.
Qed.

Definition cubicroot (z:C) := if(Rcase_abs (Re z)) then -nroot 3 (-z) else nroot 3 z.

Lemma cubicroot3 : forall z:C, Cpow (cubicroot z) 3=z.
intro.
unfold cubicroot.
induction (Rcase_abs (Re z)).
transitivity (-Cpow (nroot 3 (-z)) 3).
unfold Cpow.
field.
rewrite nroot_Cpown.
field.
discriminate.
apply nroot_Cpown.
discriminate.
Qed.

Lemma cubicrootreal : forall (x:R), 0%R=Im (cubicroot x).
  intro.
  unfold cubicroot. 
  destruct Rcase_abs as [xneg|xpos].
  transitivity (-Im(nroot 3 (-x)%R))%R.
  rewrite nrootpositive.
  rewrite Ropp_0.
  reflexivity.
  unfold RtoC,Re,fst in xneg.
  lra.
  
  repeat unfold RtoC,Im,fst,snd,Copp.
  rewrite Ropp_0.
  reflexivity.

  symmetry.
  apply nrootpositive.
  unfold Re,RtoC,fst in xpos.
  apply Rge_le.
  assumption.
Qed.

Definition CJ := ((-/2)%R,(sqrt (3/4))%R)%C.

Lemma CJ2: CJ*CJ=-CJ-1.
  unfold CJ.
Cfequal.
fold (Rsqr (sqrt (3/4))).
rewrite Rsqr_sqrt.
f_equal;
field.
lra.
Qed.

Lemma CJ3 : CJ*CJ*CJ=1%C.
rewrite CJ2.
transitivity (-(CJ*CJ)-CJ).
unfold Cpow.
field.
rewrite CJ2.
field.
Qed.

Lemma Cval2 : RtoC 2=RtoC 1+RtoC 1.
unfold Cplus,fst,snd,RtoC.
f_equal;
field.
Qed.
Lemma Cval3 : RtoC 3=RtoC 1+RtoC 1+RtoC 1.
unfold Cplus,fst,snd,RtoC.
f_equal;
field.
Qed.
Lemma Cval4: (RtoC 4=(RtoC 1+RtoC 1)*(RtoC 1+RtoC 1)).
unfold Cplus,Cmult,fst,snd,RtoC.
f_equal;
field.
Qed.
Lemma Cval6 : RtoC 6=(RtoC 1+RtoC 1+RtoC 1)*(RtoC 1+RtoC 1).
unfold Cmult,Cplus,fst,snd,RtoC.
f_equal;
field.
Qed.
Lemma Cval8 : RtoC 8=(RtoC 1+RtoC 1)*(RtoC 1+RtoC 1)*(RtoC 1+RtoC 1).
unfold Cmult,Cplus,fst,snd,RtoC.
f_equal;
field.
Qed.


Lemma shiftdeg3 : forall u:C, forall a b c:C, forall z:C, 
Cpow (z+u) 3+a*Cpow (z+u) 2+b*(z+u)+c
=Cpow z 3+(a+3*u)*Cpow z 2+(b+2*u*a+3*Cpow u 2)*z+(c+b*u+a*Cpow u 2+Cpow u 3).
intros.
unfold Cpow.
rewrite Cval3.
rewrite Cval2.
field.
Qed.

Lemma permprod: forall e f g:C,  g*f*e=e*g*f.
intros e f g.
rewrite Cmult_comm.
rewrite Cmult_assoc.
reflexivity.
Qed.

Ltac nneq0:=unfold RtoC;
injection;
intro;
lra.

Ltac developall:=
  unfold Cpow;
  repeat (try Csimpl;
          try rewrite Cmult_plus_distr_r;
          try rewrite Cmult_plus_distr_l);
  repeat (
          repeat rewrite (permprod CJ);
          repeat rewrite Cmult_assoc).




Definition Cardan_Tartaglia_formula:=fun (a1:C) (a2:C) (a3:C) (n:nat) =>
let s:=-a1/3 in 
let p:=a2+2*s*a1+3*Cpow s 2 in
let q:=a3+a2*s+a1*Cpow s 2+Cpow s 3 in
let Delta:=(Cpow (q/2) 2)+(Cpow (p/3) 3) in
let alpha : C :=if(Ceq_dec p 0) then (RtoC 0) else (cubicroot (-(q/2)+Csqrt Delta)) in
let beta:=if(Ceq_dec p 0) then -cubicroot q else -(p/3)/alpha in
s+(alpha*Cpow CJ n+beta*Cpow CJ (n+n)).


Theorem Cardan_Tartaglia : forall a1 a2 a3 :C,
let u1:=(Cardan_Tartaglia_formula a1 a2 a3 0) in
let u2:=(Cardan_Tartaglia_formula a1 a2 a3 1) in
let u3:=(Cardan_Tartaglia_formula a1 a2 a3 2) in
forall u:C, (u-u1)*(u-u2)*(u-u3)=Cpow u 3+a1*Cpow u 2+a2*u+a3.
intros.

pose (-a1/3) as s.
pose (a2+2*s*a1+3*Cpow s 2) as p.
pose (a3+a2*s+a1*Cpow s 2+Cpow s 3) as q.
pose ((Cpow (q/2) 2)+(Cpow (p/3) 3)) as Delta.
pose (if(Ceq_dec p 0) then (RtoC 0) else (cubicroot (-(q/2)+Csqrt Delta)))%C as alpha.
pose (if(Ceq_dec p 0) then -cubicroot q else -(p/3)/alpha) as beta.
pose (alpha+beta) as z1.
pose (alpha*CJ+beta*Cpow CJ 2) as z2.
pose (alpha*Cpow CJ 2+beta*CJ) as z3.
assert(u1=s+z1 /\ u2=s+z2 /\ u3=s+z3) as uv.
unfold u1,z1,u2,z2,u3,z3,Cardan_Tartaglia_formula.
fold s p q Delta alpha beta.
unfold Nat.add,Cpow.
repeat rewrite Cmult_1_r.
pose proof CJ3 as CJ3b.
rewrite<-Cmult_assoc in CJ3b.
rewrite CJ3b.
rewrite Cmult_1_r.
repeat split;reflexivity.
destruct uv as [uv1 uv2].
destruct uv2 as [uv2 uv3].
rewrite uv1.
rewrite uv2.
rewrite uv3.

assert(RtoC 1<>RtoC 0) as neq0_1 by nneq0.
assert(RtoC 2<>RtoC 0) as neq0_2 by nneq0.
assert(RtoC 3<>RtoC 0) as neq0_3 by nneq0.

assert(forall z0:C, z0<>0 -> /z0 <> 0) as invnot0.
intros z0 z0neq0.
pose proof (Cinv_r z0 z0neq0) as prodz0.
intro z0eq0.
rewrite z0eq0 in prodz0.
rewrite Cmult_0_r in prodz0.
apply neq0_1.
rewrite prodz0.
reflexivity.

assert(forall f g h:C, f+g-(g+h)=f-h) as mincancel.
intros.
field.



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
Csimpl.
repeat rewrite mincancel.
rewrite factorisationdeg3.


destruct (Ceq_dec p 0) as [peq0|pneq0].
unfold Cpow in z2,z3.
unfold z1,z2,z3,alpha.

Csimpl.
f_equal.
f_equal.
rewrite CJ2.
field.


f_equal.
rewrite peq0.
developall.
rewrite CJ3.
rewrite CJ2.
field.

developall.
rewrite CJ3.
rewrite<-(cubicroot3 q).
unfold beta.
unfold Cpow.
field.

assert((Cpow alpha 3)<>0) as alpha3neq0.

unfold alpha.
rewrite cubicroot3.


apply( (f_notequal _ _ (fun z => (q/2)+z) )).
rewrite Cplus_assoc.
Csimpl.

apply( (f_notequal _ _ (fun z => Cpow z 2) )).
unfold Cpow at 1.
rewrite Cmult_1_r.
rewrite Csqrt_Cpow2.
unfold Delta.
rewrite Cplus_comm.

apply( (f_notequal _ _ (fun z => (z+-Cpow (q/2) 2)) )).
rewrite<-Cplus_assoc.
Csimpl.

unfold Cpow.
repeat apply Cmult_neq_0;
try apply invnot0;
try assumption.

assert (alpha<>0) as alphaneq0.
apply( (f_notequal _ _ (fun z => Cpow z 3))).
unfold Cpow at 2.
repeat rewrite Cmult_0_l.
assumption.


f_equal.
f_equal.
f_equal.
replace (z1+z2+z3) with (RtoC 0).
Csimpl.
reflexivity.

unfold z1,z2,z3.
unfold Cpow.
developall.
rewrite CJ2.
field.


f_equal.
unfold z1,z2,z3.

unfold Cpow.

developall.
rewrite CJ3.
repeat rewrite Cmult_1_l.
rewrite CJ2.
unfold Cminus.
developall.

transitivity(-(3*alpha*beta)).
rewrite Cval3.
field.
unfold beta.
field; try (split; [ nneq0 | ]).
assumption.

unfold z1,z2,z3.
developall.
rewrite CJ3.
rewrite CJ2.
developall.

transitivity(-(Cpow alpha 3+Cpow beta 3)).
unfold Cpow.
field.

transitivity(--q).
f_equal.
rewrite<-Cmult_1_r at 1.
rewrite<-Cmult_1_r.
rewrite<-(Cinv_r (Cpow alpha 3)).
repeat rewrite Cmult_assoc.
f_equal.
rewrite Cmult_plus_distr_r.
rewrite<-(comCpow _ beta alpha).
unfold beta.
unfold Cdiv.
rewrite<-Cmult_assoc.
rewrite Cinv_l.
fold (Cdiv p 3).
unfold alpha.
rewrite cubicroot3.
developall.

rewrite Csqrt_Cpow2.
generalize (Csqrt Delta).
intro.
unfold Delta,Cpow.
rewrite Cval2.
field; split; nneq0.

assumption.
assumption.
field.

Qed.

Lemma shiftdeg4 : forall u:C, forall a b c d:C, forall z:C, 
Cpow (z+u) 4+a*Cpow (z+u) 3+b*Cpow (z+u) 2+c*(z+u)+d
=Cpow z 4+(a+4*u)*Cpow z 3+(b+3*u*a+6*Cpow u 2)*Cpow z 2
 +(c+2*b*u+3*a*Cpow u 2+4*Cpow u 3)*z+(d+c*u+b*Cpow u 2+a*Cpow u 3+Cpow u 4).
intros.
unfold Cpow.
rewrite Cval6.
rewrite Cval4.
rewrite Cval3.
rewrite Cval2.
field.
Qed.

Definition binom_solution:= fun (b:C) (c:C) (n:nat) =>
-b/2+(Csqrt (Cpow (b/2) 2-c))*Cpow (-1) n.

Lemma Binom_solution_proof : forall (b:C) (c:C), forall z:C,
Cpow z 2+b*z+c=(z-binom_solution b c 0)*(z-binom_solution b c 1).
intros.
transitivity (Cpow z 2+-(binom_solution b c 0+binom_solution b c 1)*z
              +(binom_solution b c 0)*(binom_solution b c 1)).
unfold binom_solution.
unfold Cpow.
f_equal.
f_equal.
f_equal.
repeat rewrite Cmult_1_r.
assert(forall (f:C) (g:C), (f+g)+(f+g*(-1))=f+f) as aux1.
intros.
destruct f,g.
unfold RtoC,Cmult,Copp,Cplus,fst,snd.
f_equal;field.
rewrite aux1.
rewrite Cval2.
field; nneq0.

repeat rewrite Cmult_1_r.
assert(forall u v :C, (u+v)*(u+v*-1)=u*u-v*v) as diffsq.
intros.
destruct u,v.
unfold RtoC,Cminus,Cmult,Copp,Cplus,fst,snd.
f_equal;field.
rewrite diffsq.
rewrite Csqrt_Cpow2.
field; nneq0.
unfold Cpow.
field.
Qed.

Theorem Ferrari_formula: forall (a:C) (b:C) (c:C) (d:C), 
let s:=-a/4 in 
let p:= b+3*s*a+6*Cpow s 2 in
let q:= c+2*b*s+3*a*Cpow s 2+4*Cpow s 3 in
let r:= d+c*s+b*Cpow s 2+a*Cpow s 3+Cpow s 4 in
let lambda:=Cardan_Tartaglia_formula (-p/2) (-r) (r*p/2-/8*Cpow q 2) 0 in
let A:=Csqrt(2*lambda-p) in
let cond:=(Ceq_dec (2*lambda) p) in
let B:=if cond then (RtoC 0) else (-q/(2*A)) in
let z1:=if cond then Csqrt (binom_solution p r 0) 
                else binom_solution A (B+lambda) 0 in
let z2:=if cond then -Csqrt (binom_solution p r 0) 
                else binom_solution A (B+lambda) 1 in
let z3:=if cond then Csqrt (binom_solution p r 1) 
                else binom_solution (-A) (-B+lambda) 0 in
let z4:=if cond then -Csqrt (binom_solution p r 1) 
                else binom_solution (-A) (-B+lambda) 1 in
let u1:=z1+s in
let u2:=z2+s in
let u3:=z3+s in
let u4:=z4+s in
forall u:C, (u-u1)*(u-u2)*(u-u3)*(u-u4)=Cpow u 4+a*Cpow u 3+b*Cpow u 2+c*u+d.

assert(forall w x:C, (w+-x)=0 -> w=x) as cancelm.
intros w x diff.
rewrite<-(Cplus_0_l w).
rewrite<-(Cplus_opp_r x).
rewrite<-Cplus_assoc.
rewrite (Cplus_comm _ w).
rewrite diff.
rewrite Cplus_0_r.
reflexivity.

intros.
unfold u1,u2,u3,u4.
pose (z:=u-s).
assert(u=z+s) as Hszu.
unfold z.
field.
rewrite Hszu.
rewrite (shiftdeg4 s).
fold p.
fold q.
fold r.
assert(forall f g h:C, f+g-(h+g)=f-h) as mincancel.
intros.
field.
repeat rewrite mincancel.
unfold s.
unfold Cdiv.
rewrite (Cmult_comm _ (/4)).
rewrite (Cmult_assoc 4).
rewrite Cinv_r; [ | nneq0 ].
rewrite Cmult_1_l.
rewrite Cplus_opp_r.
rewrite Cmult_0_l.
rewrite Cplus_0_r.
pose proof (Cardan_Tartaglia (- p / 2) (- r) 
            (r*p / 2 - / 8 * Cpow q 2) lambda) as Hlambda.
fold lambda in Hlambda.
unfold Cminus in Hlambda at 1.
rewrite Cplus_opp_r in Hlambda.
repeat rewrite Cmult_0_l in Hlambda.


destruct cond as [cond|cond].

assert(forall f g:C,(f-g)*(f--g)=f*f-g*g) as diffsqr.
intros.
field.

unfold z1,z2.
rewrite diffsqr.

rewrite<-Cmult_assoc.
unfold z3,z4.
rewrite diffsqr.
repeat rewrite Csqrt_Cpow2.
rewrite <-Binom_solution_proof.

rewrite<-cond in Hlambda.
assert(/8*Cpow q 2=0) as aux.
rewrite<-Copp_0.
rewrite Hlambda.
unfold Cpow,Cdiv,Cminus.
field; split; nneq0.
unfold Cpow in aux.
rewrite Cmult_1_r in aux.
assert(q=0) as q0.
destruct (Ceq_dec q 0) as [Hq | Hq].
assumption.
exfalso.

apply (Cmult_neq_0 (/8) (q*q)).
nneq0.
apply (Cmult_neq_0 q q);
assumption.
assumption.

rewrite q0.
unfold Cpow.
field.

assert(A<>0) as Aneq0.
intro Aeq0.
assert(A*A=0) as A2eq0.
rewrite Aeq0.
apply Cmult_0_r.
unfold A in A2eq0.
rewrite Csqrt_Cpow2 in A2eq0.
apply cond.
apply cancelm.
apply A2eq0.


unfold z1.
unfold z2.
rewrite<-Binom_solution_proof.
rewrite<-Cmult_assoc.
unfold z3.
unfold z4.
rewrite<-Binom_solution_proof.
transitivity (Cpow z 4+(-(A*A)+2*lambda)*Cpow z 2
             +(-((A*B)*2))*z+(lambda*lambda+-(B*B))).

unfold Cpow.

rewrite Cval2.
field.

replace (A*B) with (-q/2).
replace (B*B) with (q*q/((A*A)*4)).
unfold A.
rewrite Csqrt_Cpow2.
f_equal.
f_equal.
f_equal.
field.
field; nneq0.
apply cancelm.
rewrite<-(Cmult_0_r (/(lambda-p/2))).
rewrite Hlambda.
rewrite Cval8.
rewrite Cval4.
rewrite Cval2.
unfold Cpow.
field.
try (split; [ nneq0 | ]; split; [ nneq0 | ]; split; [ | nneq0 ]).
apply Cminus_eq_contra.
intro hypabs.
apply cond.
rewrite<-hypabs.
destruct lambda.
unfold Cmult,RtoC,fst,snd.
f_equal; field; nneq0.
unfold B.
unfold Cdiv.
rewrite Cval2.
rewrite Cval4.
field; try (split; [ | split; nneq0 ]).
assumption.
unfold B,Cdiv.
field; try (split; [ | nneq0 ]).
assumption.
Qed.
