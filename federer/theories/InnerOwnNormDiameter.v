(** Federer (1969), 3.2.35, p. 271:
    boundedness of the convex body is unchanged
    when its inner-product metric is expressed by
    the same abstract norm metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  NormMetric MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [inner_own_norm_diameter]: supporting
    exact metric compatibility in Federer 3.2.35,
    p. 271, by the norm convention of
    1.7.1, p. 28. The two metrics have
    identical pairwise distances; their independent
    sealed least-bound diameter laws therefore agree
    on every subset, including empty and unbounded sets. *)
Lemma inner_own_norm_diameter (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V):
  @extended_metric_diameter R
    [the metricType R of real_norm_metric_space (inner_norm_real_norm hB)] A=
  @extended_metric_diameter R [the metricType R of inner_metric_space hB] A.
Proof.
pose X:=[the metricType R of inner_metric_space hB].
pose Y:=[the metricType R of real_norm_metric_space (inner_norm_real_norm hB)].
pose D:=@extended_metric_diameter R X A.
have hD:=@extended_metric_diameter_specification R X A.
apply:(@metric_diameter_unique R Y A _ D (@extended_metric_diameter_specification R Y A)).
constructor.
- exact:metric_diameter_nonnegative hD.
- move=>x y hx hy; exact:(@metric_diameter_upper R X A D hD x y hx hy).
- move=>b hb hBound.
  apply:(@metric_diameter_least R X A D hD b hb).
  by move=>x y hx hy; exact:(hBound x y hx hy).
Qed.

(** Source for [inner_own_norm_bounded_iff]: supporting
    preservation of the bounded-body hypothesis in
    Federer 3.2.35, p. 271. This is
    exactly the proved all-set diameter identity
    and the existing finite-diameter definition. *)
Lemma inner_own_norm_bounded_iff (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (A:set V):
  @metric_set_bounded R [the metricType R of inner_metric_space hB] A <->
  @metric_set_bounded R
    [the metricType R of real_norm_metric_space (inner_norm_real_norm hB)] A.
Proof. by rewrite /metric_set_bounded inner_own_norm_diameter. Qed.
