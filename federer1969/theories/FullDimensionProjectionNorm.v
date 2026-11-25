(** Federer (1969), 2.10.35, p. 197: beta_t(n,n)= 1. Equal-dimension
    projections are orthogonal automorphisms, so their top exterior products
    preserve norm. Evaluate the existing projection-constant specification
    on a simple unit vector and use the constant probability norm. No
    relevant working-erratum correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric CoordinateProjection
  FullDimensionProjections EuclideanProjectionSpace EuclideanProjectionMetric
  ExteriorGrading ExteriorNorm ExteriorProjectionNorm ExteriorDiameterUP OrthogonalProjectionConstants ProjectionBeta
  ProjectionBetaContinuity OrthogonalProjectionProbability
  NonnegativeExtendedProbabilityConstant NonnegativeExtendedScalarNorm
  RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionBasic MeasurableTotalBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_dimension_projection_exterior_norm]: supporting
    norm-preservation step behind beta_t(n,n)= 1
    in 2.10.35, p. 197, from
    the orthogonal exterior-map laws of 1.7.6. *)
Lemma equal_dimension_projection_exterior_norm (R : realType) (n : nat)
    (xi : exterior_power (R_n R n) n)
    (p : orthogonal_projection_metric_space R n n) :
  projection_norm (real_exterior_two_nonzero R) xi p=
    exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R n) xi.
Proof.
apply: (@exterior_orthogonal_norm R (real_exterior_two_nonzero R)
  (R_n R n) (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) (euclidean_projection_linear p)).
exact: equal_dimension_projection_orthogonal (euclidean_projection_linear_member p).
Qed.

(** Source for [equal_dimension_projection_beta]: direct
    beta_t(n,n)= 1 used in 2.10.35,
    p. 197. The calculation covers
    all 1<=t<=infinity and natural dimension zero. *)
Theorem equal_dimension_projection_beta (R : realType) (n : nat)
    (hnn : (n<=n)%N) (t : \bar R) :
  (1<=t)%E -> @projection_beta R n n hnn t= 1.
Proof.
move=> ht.
have [xi [hs hu]] := @euclidean_simple_unit_vector_exists R n n hnn.
have hb := @projection_beta_scalar_norm_value R n n hnn xi t hs hu ht.
have he : (fun p : orthogonal_projection_metric_space R n n=>
    (projection_norm (real_exterior_two_nonzero R) xi p : real_norm_metric_space (scalar_absolute_value_norm R)))=
    (fun _=>1).
  by apply: funext=> p; rewrite equal_dimension_projection_exterior_norm hu.
rewrite he in hb.
have hm := @theta_star_is_measure R n n hnn.
have hprob := @theta_star_total R n n hnn.
have hf := @measurable_total_constant R (orthogonal_projection_metric_space R n n)
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] _ hm 1.
have hn := @nonnegative_extended_norm_scalar_embedding R (orthogonal_projection_metric_space R n n)
  _ hm (fun _=> (1 : real_norm_metric_space (scalar_absolute_value_norm R))) t
  (fun _=>@ler01 R) ht hf.
rewrite (@probability_extended_norm_one R (orthogonal_projection_metric_space R n n) _ hm t hprob ht) in hn.
have heq := eq_trans hn hb.
exact: EFin_inj (esym heq).
Qed.
