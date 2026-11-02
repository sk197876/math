(** Federer (1969), 2.4.13, p. 88: the weighted arithmetic-geometric mean
    inequality, with equality exactly when the two bases agree. The argument
    below proves strict concavity of log from its tangent inequality, then
    applies exp as in the book. No relevant entry occurs in Federer's
    erratum for this item. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower
  WeightedMeanAlgebra RealLogarithmConcavity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_arithmetic_geometric_mean_positive]:
    direct inequality in Federer 2.4.13, p. 88,
    for positive bases and weights summing to one. *)
Theorem weighted_arithmetic_geometric_mean_positive (R : realType) (a b x y : R) :
  0 < a -> 0 < b -> a+b = 1 -> 0 < x -> 0 < y ->
  real_power x a * real_power y b <= a*x+b*y.
Proof.
move=> ha hb hab hx hy; have hw := positive_weighted_mean ha hb hx hy.
rewrite !real_power_positive_base // -(real_exponential_add (@RealExponential.laws R))
  -(real_exponential_logarithm (@RealExponential.laws R) hw) real_exponential_order.
exact: real_logarithm_weighted_concavity ha hb hab hx hy.
Qed.

(** Source for [weighted_arithmetic_geometric_mean_strict]:
    strict inequality for unequal bases, giving the equality
    criterion in Federer 2.4.13, p. 88. *)
Lemma weighted_arithmetic_geometric_mean_strict (R : realType) (a b x y : R) :
  0 < a -> 0 < b -> a+b = 1 -> 0 < x -> 0 < y -> x != y ->
  real_power x a * real_power y b < a*x+b*y.
Proof.
move=> ha hb hab hx hy hxy; have hw := positive_weighted_mean ha hb hx hy.
rewrite !real_power_positive_base // -(real_exponential_add (@RealExponential.laws R))
  -(real_exponential_logarithm (@RealExponential.laws R) hw)
  (real_exponential_strict_order (@RealExponential.laws R)).
exact: real_logarithm_weighted_strict_concavity ha hb hab hx hy hxy.
Qed.

(** Source for [weighted_arithmetic_geometric_mean]: Supporting Federer
    2.4.13, p. 88.The weights remain strictly positive. *)
Theorem weighted_arithmetic_geometric_mean (R : realType) (a b x y : R) :
  0 < a -> 0 < b -> a+b = 1 -> 0 <= x -> 0 <= y ->
  real_power x a * real_power y b <= a*x+b*y.
Proof.
move=> ha hb hab hx hy; have [->|hx0] := eqVneq x 0.
  rewrite real_power_zero_base ?gt_eqF // mul0r mulr0 add0r; exact: mulr_ge0 (ltW hb) hy.
have [->|hy0] := eqVneq y 0.
  rewrite real_power_zero_base ?gt_eqF // !mulr0 addr0; exact: mulr_ge0 (ltW ha) hx.
apply: weighted_arithmetic_geometric_mean_positive ha hb hab _ _;
  by rewrite lt_neqAle eq_sym ?hx0 ?hy0 ?hx ?hy.
Qed.

(** Source for [weighted_arithmetic_geometric_mean_equality]: equality
    exactly for equal bases in Federer 2.4.13, p. 88, including nonnegative
    bases. *)
Theorem weighted_arithmetic_geometric_mean_equality (R : realType) (a b x y : R) :
  0 < a -> 0 < b -> a+b = 1 -> 0 <= x -> 0 <= y ->
  (real_power x a * real_power y b = a*x+b*y <-> x=y).
Proof.
move=> ha hb hab hx hy; split.
- move=> he; have [hx0|hx0] := eqVneq x 0.
  + move: he; rewrite hx0 real_power_zero_base ?gt_eqF // mul0r mulr0 add0r.
    move/eqP; rewrite eq_sym mulf_eq0 (gt_eqF hb) /= => /eqP hy0.
    by rewrite hy0.
  + have [hy0|hy0] := eqVneq y 0.
    * move: he; rewrite hy0 real_power_zero_base ?gt_eqF // !mulr0 addr0.
      move/eqP; rewrite eq_sym mulf_eq0 (gt_eqF ha) /= => /eqP hxz.
      by rewrite hxz.
    * have [hexy|hxy] := eqVneq x y; first exact hexy.
      exfalso.
      have hxpos : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
      have hypos : 0 < y by rewrite lt_neqAle eq_sym hy0 hy.
      have hlt := weighted_arithmetic_geometric_mean_strict ha hb hab hxpos hypos hxy.
      by move: hlt; rewrite he ltxx.
- move=> ->; have [->|hy0] := eqVneq y 0.
  + by rewrite !real_power_zero_base ?gt_eqF // !mul0r !mulr0 addr0.
  + have hypos : 0 < y by rewrite lt_neqAle eq_sym hy0 hy.
    rewrite !real_power_positive_base // -(real_exponential_add (@RealExponential.laws R))
      -!mulrDl hab !mul1r (real_exponential_logarithm (@RealExponential.laws R)) //.
Qed.
