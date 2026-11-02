(** Federer (1969), 2.4.17, p. 90: the powered factors used in Holder
    interpolation. The supporting graph identity retains the exact partial
    domain, including zero values. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormPower
  PartialNormProduct NormPowerScalar RealPower RealPowerSuccessor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [norm_power_product_graph]: supporting product identity for
    the Holder argument in Federer 2.4.17, p. 90 *)
Lemma norm_power_product_graph (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (f : partial_function X V) (r s : R) x z :
  (0 < r)%R -> (0 < s)%R ->
  (partial_function_graph
    (partial_norm_product (fun a : R => `|a|%R) (fun a : R => `|a|%R)
      (partial_scalar_norm_power N r f) (partial_scalar_norm_power N s f)) x z <->
   partial_function_graph (partial_norm_power N (r+s)%R f) x z).
Proof.
move=> hr hs.
have he y : (`|real_power (N y) r| * `|real_power (N y) s|)%R = real_power (N y) (r+s)%R.
  rewrite !ger0_norm ?real_power_nonnegative //.
  have [hy0|hy0] := eqVneq (N y) 0%R.
  - by rewrite hy0 !real_power_zero_base ?gt_eqF ?addr_gt0 // mul0r.
  have hyp : (0 < N y)%R by rewrite lt_neqAle eq_sym hy0 (real_seminorm_nonnegative hN.1 y).
  symmetry; exact: real_power_add_exponents_positive.
rewrite (@partial_norm_product_graph R X R^o R^o _ _ (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)).
split.
- move=> [a [b [[y [hy hya]] [[v [hv hvb]] hab]]]].
  have hyv := partial_function_single_valued hy hv.
  exists y; split=> //; by rewrite -hya -hvb -hyv he in hab.
- move=> [y [hy hyz]]; exists (real_power (N y) r),(real_power (N y) s).
  split; first by exists y; split.
  split; first by exists y; split.
  by rewrite he.
Qed.
