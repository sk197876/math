(** Federer (1969), 2.6.6, pp. 120–121: the norm bound needed for extension
    to an inverse limit. Consistency and compactness give the bound on the
    actual limit, even when its projections are not onto the factor spaces.
    Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseLimitClosedCoordinate CompactContinuousPullback CompactSupportFunctionUP
  UniformFunctionNorm UniformFunctionNormUP NormalizedDaniellUniformLipschitz
  RealMetricBackground MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_daniell_pullback_norm_bound]: the bound
    needed to repeat |gamma|<=nu for inverse limits in Federer
    2.6.6, pp. 120–121. The proof uses later bonding-map
    images and does not assume a surjective projection. *)
Theorem inverse_daniell_pullback_norm_bound (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R) (u0 : prod_topology Y) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  is_consistent_inverse_daniell_family le b A -> forall i (f : Y i -> R),
  compactly_supported_continuous_functions f -> `|A i f|<=compact_support_uniform_norm (f \o p i).
Proof.
move=> hs hl hA i f hf.
have hfp := @compact_continuous_pullback_membership R X (Y i) (p i) f
  (compact_inverse_limit_compact hl) (@compact_inverse_limit_projection_continuous I le Y b X p hl i) hf.
pose n := compact_support_uniform_norm (f \o p i).
have hn := compact_support_uniform_norm_specification hfp.
apply/ler_addgt0Pr=> e he.
pose V : set (real_line_metric R) := [set r | mdist (0 : real_line_metric R) r<n+e].
pose U := (f : Y i -> real_line_metric R) @^-1` V.
have hV : open V := metric_open_ball_open (0 : real_line_metric R) (n+e).
have hU : open U.
  rewrite openE=> y hy; apply: hf.1; move: hV; rewrite openE=> hv; exact: hv _ hy.
have hpU : forall x, U (p i x).
  move=> x; change (is_true (mdist (0 : real_line_metric R) (f (p i x))<n+e)).
  rewrite real_line_metric_distanceE sub0r normrN.
  have hne : n<n+e by rewrite ltrDl.
  exact: le_lt_trans (uniform_function_norm_bound hn x) hne.
have [j [hij hj]] := @inverse_limit_projection_neighborhood I le Y b X p u0 i U hs hl hU hpU.
have hfj := @compact_continuous_pullback_membership R (Y j) (Y i) (b i j) f
  (@compact_inverse_system_compact I le Y b hs j) (@compact_inverse_system_continuous I le Y b hs i j hij) hf.
rewrite -(@inverse_daniell_family_consistent R I le Y b A hA i j hij f hf).
apply: le_trans (@normalized_daniell_uniform_bound R (Y j) (A j)
  (@compact_inverse_system_compact I le Y b hs j) (@inverse_daniell_family_integral R I le Y b A hA j)
  (@inverse_daniell_family_one R I le Y b A hA j) _ hfj) _.
apply: (@uniform_function_norm_least R (Y j) _ _ (compact_support_uniform_norm_specification hfj) (n+e)).
- exact: addr_ge0 (uniform_function_norm_nonnegative hn) (ltW he).
- move=> y; apply: ltW; have hy := hj y.
  change (is_true (mdist (0 : real_line_metric R) (f (b i j y))<n+e)) in hy.
  by move: hy; rewrite real_line_metric_distanceE sub0r normrN.
Qed.
