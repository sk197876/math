(** The partial function S maps to integral_S f dphi divided by phi(S), in
    Federer (1969), 2.9.8, p. 156. Its graph specifies an actual subset
    integral and the ordinary partial quotient; it does not select arbitrary
    values when either is undefined. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealConventions PartialFunctionUP
  PartialZeroExtension MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  MeasureAlmostUP PartialExtendedOrderLoci MeasurableFunctionUP
  MeasureDensityUP MeasureDensity MeasureDerivates DerivationIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_mean_function]: direct partial
    integral quotient in the conclusion of Federer 2.9.8,
    p. 156. Single-valuedness follows from
    uniqueness of subset integrals; no construction
    of an integral value is exposed. *)
Definition measure_mean_function (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
    partial_function (set X) (\bar R).
Proof.
refine (@Build_partial_function (set X) (\bar R)
  (fun S y => exists a, is_measure_subset_integral phi S f a /\ extended_divide a (phi S)=Some y) _).
move=> S y z [a [ha hey]] [b [hb hez]].
have he := @measure_integral_unique R X phi (partial_function_zero_extension (0 : extended_real_line R) S f) a b ha hb.
rewrite -he in hez; rewrite hey in hez; by case: hez.
Defined.

(** Source for [measure_mean_zero_denominator]: ordinary
    division-domain qualification for the mean in Federer
    2.9.8, p. 156, under the arithmetic
    convention 2.1.1, p. 51. Even if
    a zero subset integral exists, 0/0 is undefined. *)
Lemma measure_mean_zero_denominator (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) S :
  phi S=0 -> ~ partial_function_domain (measure_mean_function phi f) S.
Proof.
move=> hz [y [a [_ hdiv]]]; move: hdiv; rewrite hz extended_divide_zero; discriminate.
Qed.

(** Source for [nonnegative_mean_density_graph]: the identification of
    psi(S)/phi(S) with the integral mean in Federer 2.9.8, p. 156 It applies
    to every measurable cell, including cells of infinite measure,
    preserving undefined quotients. *)
Lemma nonnegative_mean_density_graph (R : realType) (X : choiceType)
    (phi nu : set X -> \bar R) (f : partial_function X (extended_real_line R)) S y :
  is_measure phi -> is_measure_density phi f nu -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) -> measure_measurable phi S ->
  (partial_function_graph (measure_mean_function phi f) S y <->
   partial_function_graph (measure_ratio_function nu phi) S y).
Proof.
move=> hm hn hf hp hS.
have hi := @nonnegative_density_subset_integral R X phi f S hm hf hp hS.
have he := @measure_density_unique R X phi f nu (measure_with_density phi f) hn (measure_with_density_laws phi f) S.
rewrite -he in hi.
split.
- move=> [a [ha hdiv]].
  have eav := @measure_integral_unique R X phi
    (partial_function_zero_extension (0 : extended_real_line R) S f) a (nu S) ha hi.
  by move: hdiv; rewrite eav.
- move=> hdiv; exists (nu S); by split.
Qed.
