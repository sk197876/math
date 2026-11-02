(** Federer (1969), 2.9.12, pp. 158–159: densities and approximate limits of
    functions on partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureDerivationContext
  MeasureSetDensity MeasureApproximateLimitUP MeasureApproximateOrderLimits
  ZeroDensityCover ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [whole_set_density_not_zero]: supporting nondegeneracy for
    the uniqueness assertion in Federer 2.9.12, p. 158 This concerns actual
    graph values, including null reference measures, for which the density
    graph is empty. *)
Lemma whole_set_density_not_zero (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  is_measure_derivation_context phi V ->
  ~ partial_function_graph (measure_set_density phi V setT) x 0.
Proof.
move=> hc hz; apply: (@zero_density_cover_impossible R X phi V setT setT x hc _ hz hz).
by rewrite setUT.
Qed.

(** Source for [empty_function_no_approximate_limit]: partial-domain
    boundary supporting Federer 2.9.12, pp. 158–159. The
    missing domain is all of X, whose density cannot be zero.
    This holds even for a null reference measure. *)
Lemma empty_function_no_approximate_limit (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop) x y :
  is_measure_derivation_context phi V ->
  ~ is_measure_approximate_limit phi V (@partial_function_empty X Y) x y.
Proof.
move=> hc hl; have hd := approximate_limit_domain_density hl.
rewrite partial_function_empty_domain setC0 in hd.
exact: whole_set_density_not_zero hc hd.
Qed.

(** Source for [empty_function_approximate_order_limits]: regression
    consequence of Federer 2.9.12, p. 159, as corrected by erratum p. 3,
    book p. 159 line 7. Empty-domain functions have upper approximate limit
    +infinity and lower approximate limit -infinity. The raw strict level
    sets would miss this correction *)
Lemma empty_function_approximate_order_limits (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  is_measure_derivation_context phi V ->
  measure_approximate_upper_limit phi V (@partial_function_empty X (\bar R)) x=+oo /\
  measure_approximate_lower_limit phi V (@partial_function_empty X (\bar R)) x= -oo.
Proof.
move=> hc.
have hpre (W : set (\bar R)) :
    partial_function_preimage (@partial_function_empty X (\bar R)) W=set0.
  apply/seteqP; split=> a; first by move=> [v [[] _]].
  by move=> [].
have hu : measure_approximate_upper_thresholds phi V (@partial_function_empty X (\bar R)) x=set0.
  apply/seteqP; split=> t; last by move=> [].
  rewrite /measure_approximate_upper_thresholds /= hpre setC0.
  exact: whole_set_density_not_zero hc.
have hl : measure_approximate_lower_thresholds phi V (@partial_function_empty X (\bar R)) x=set0.
  apply/seteqP; split=> t; last by move=> [].
  rewrite /measure_approximate_lower_thresholds /= hpre setC0.
  exact: whole_set_density_not_zero hc.
by rewrite /measure_approximate_upper_limit /measure_approximate_lower_limit hu hl
  extended_real_inf_empty extended_real_sup_empty.
Qed.
