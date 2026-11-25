(** Federer (1969), 1.7.5, p. 33: Cauchy's inequality applied to the sum
    over S(nu). The proof instantiates the project's 1.7.1 Cauchy inequality
    on a finite coordinate space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerCauchy EuclideanInnerProduct GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_sum_cauchy_squared]: Federer 1.7.5,
    p. 33, the square of a finite sum is at most its
    number of terms times the sum of their squares. Empty sums
    are included. *)
Theorem finite_sum_cauchy_squared (R : realFieldType) (I : finType)
    (P : pred I) (a : I -> R) :
  (\sum_(i | P i) a i)^+2 <= (#|P|)%:R * \sum_(i | P i) (a i)^+2.
Proof.
pose x : R_n R #|P| := [ffun i => a (@enum_val I P i)].
pose y : R_n R #|P| := [ffun _ => 1].
have hh := @inner_cauchy_squared R (R_n R #|P|) (@euclidean_inner_product R #|P|)
  (@euclidean_inner_productP R #|P|) x y.
have hxy : euclidean_inner_product x y = \sum_(i | P i) a i.
  rewrite /euclidean_inner_product (big_enum_val a); apply: eq_bigr => i _.
  by rewrite /x /y !ffunE mulr1.
have hxx : euclidean_inner_product x x = \sum_(i | P i) (a i)^+2.
  rewrite /euclidean_inner_product (big_enum_val (fun i => (a i)^+2)); apply: eq_bigr => i _.
  by rewrite /x !ffunE expr2.
have hyy : euclidean_inner_product y y = (#|P|)%:R.
  rewrite /euclidean_inner_product.
  under eq_bigr do rewrite /y !ffunE mul1r.
  by rewrite sumr_const card_ord.
by rewrite hxy hxx hyy mulrC in hh.
Qed.
