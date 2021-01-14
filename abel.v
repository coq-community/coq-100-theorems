From mathcomp Require Import all_ssreflect all_algebra all_field.
From Abel Require Import abel.


Lemma example_not_solvable_by_radicals :
  ~ solvable_by_radical_poly ('X^5 - 4%:R *: 'X + 2%:R : {poly rat}).
