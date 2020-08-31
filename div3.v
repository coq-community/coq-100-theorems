(*
MIT License

Copyright (c) 2014 Jean-Marie Madiot, ENS Lyon

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
