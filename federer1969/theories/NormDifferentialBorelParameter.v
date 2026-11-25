(** Federer (1969), 3.1.1, p. 211: apply the injective Borel
    projection theorem after representing the differential values
    in a complete separable operator space. This adapter allows
    that space to be the operators into a closed target subspace. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis NormDifferentialUP
  NormDifferentialDirectional NormClassOneUP ContinuousOperatorUP ContinuousOperatorNorm
  NormDifferentialBorelGraph FiniteNormMetricPolish CompleteMetricUP MetricProductBackground
  TopologicalProductMaps TopologicalBorel ContinuousBorelPreimages BorelSingleValuedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_borel_parameter_preimage]:
    supporting Borel projection step in 3.1.1, p. 211. An
    injective continuous operator parameterisation need cover
    only the actual differential values, not every ambient operator. *)
Theorem norm_differential_borel_parameter_preimage (R : realType)
    (X Y Z : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (evaluation : Hom Z (Hom X Y)) (ZN : Z -> R)
    (hZ : is_continuous_operator_space NX NY evaluation ZN)
    n (e : 'I_n -> X) (he : is_basis e) (A : set X) (f : X -> Y)
    (W : metricType R)
    (j : W -> real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)) :
  norm_class_zero NX NY A f -> is_complete_metric_space W ->
  (exists D : set W, countable D /\ dense D) -> continuous j -> injective j ->
  (forall a L, has_norm_differential NX NY A f a L -> exists w, evaluation (j w)=L) ->
  forall B : set (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)),
    borel_set B -> @borel_set [the topologicalType of real_norm_metric_space hNX]
      [set a | exists z, has_norm_differential NX NY A f a (evaluation z) /\ B z].
Proof.
move=> hf hW hsW hj hinj hcover B hB.
pose E := real_norm_metric_space hNX.
pose T := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose P := [the metricType R of metric_product E W].
pose G := @norm_differential_operator_graph R X Y Z NX NY hNX hNY evaluation ZN hZ A f.
pose k := fun p : P => ((p.1,j p.2) : metric_product E T).
have hk : continuous k.
  apply: topological_pair_continuous; first exact: first_projection_continuous.
  move=> p; exact: continuous_comp (@second_projection_continuous E W p) (hj p.2).
have hG : borel_set (k @^-1` G).
  apply: (continuous_borel_preimage hk).
  exact: (@norm_differential_operator_graph_borel R X Y Z NX NY hNX hNY evaluation ZN hZ A f hf).
have hu : forall a u v, (k @^-1` G) (a,u) -> (k @^-1` G) (a,v) -> u=v.
  move=> a u v hdu hdv; apply: hinj; apply: (continuous_operator_injective hZ).
  exact: (@norm_differential_unique R X Y NX NY hNX hNY A f a (evaluation (j u))
    (evaluation (j v)) hdu hdv).
have hb := @borel_single_valued_graph_preimage R E W (k @^-1` G)
  (@finite_norm_metric_complete R X NX hNX n e he) hW
  (@finite_norm_metric_separable R X NX hNX n e he) hsW hG hu
  (j @^-1` B) (continuous_borel_preimage hj hB).
have heq : [set a : E | exists z, has_norm_differential NX NY A f a (evaluation z) /\ B z]=
    [set a : E | exists w, (k @^-1` G) (a,w) /\ (j @^-1` B) w].
  apply/seteqP; split=> a.
  - move=> [z [hd hz]].
    have [w hw] := hcover a (evaluation z) hd.
    have hew : j w=z := continuous_operator_injective hZ hw.
    exists w; split.
    + change (has_norm_differential NX NY A f a (evaluation (j w))); by rewrite hew.
    + change (B (j w)); by rewrite hew.
  - move=> [w [hd hw]]; by exists (j w).
by rewrite heq.
Qed.
