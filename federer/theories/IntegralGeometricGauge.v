(** Federer (1969), 2.10.5, p. 172, first displayed definition, paraphrased:
    zeta_t(S) is the theta* L^t norm of f_S divided by beta_t(n,m). Both
    theta* and beta are the actual sealed objects characterized by
    2.7.16(6), pp. 139–140. Nonnegative extended projected volumes retain
    infinite values in the norm formulas of 2.4.12, p. 86. The source's
    positive-degree and m<=n setting is retained for the measures; these
    supporting gauge laws also allow degree zero under the established
    Lebesgue empty-product convention. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  OrthogonalProjectionProbability ProjectedVolumeMeasurability ProjectionBeta
  NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm
  SuslinSetUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge]: direct
    gauge zeta_t(S) in Federer 2.10.5, p. 172,
    for the actual normalized projection probability
    and the original positive projection constant. *)
Definition integral_geometric_gauge (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :=
  (@projection_beta R n m hmn t)^-1%R%:E *
    nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
      (projected_volume_function (m:=m) S) t.

(** Source for [integral_geometric_gauge_normalized]:
    direct numerator identity beta_t zeta_t(S)
    in Federer 2.10.5, p. 172. Positivity
    of the actual beta justifies cancellation,
    including an infinite numerator. *)
Lemma integral_geometric_gauge_normalized (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) (ht : 1<=t)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (@projection_beta R n m hmn t)%:E * @integral_geometric_gauge R n m hmn t S =
    nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
      (projected_volume_function (m:=m) S) t.
Proof.
have hb : (@projection_beta R n m hmn t!=0)%R.
  by rewrite gt_eqF //; exact: projection_beta_positive.
by rewrite /integral_geometric_gauge muleA -EFinM mulfV // mul1e.
Qed.

(** Source for [integral_geometric_gauge_norm_specification]:
    direct norm characterization of beta_t zeta_t(S)
    in Federer 2.10.5, p. 172, for every
    Suslin S. It includes the actual power integral
    for finite t and null-superlevel bounds for infinity. *)
Theorem integral_geometric_gauge_norm_specification (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) (ht : 1<=t)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> is_nonnegative_extended_exponent_norm
    (@orthogonal_projection_probability R n m hmn) (projected_volume_function (m:=m) S) t
    ((@projection_beta R n m hmn t)%:E * @integral_geometric_gauge R n m hmn t S).
Proof.
move=> hS; rewrite (@integral_geometric_gauge_normalized R n m hmn t ht S).
exact (@nonnegative_extended_exponent_norm_specification R _
  (@orthogonal_projection_probability R n m hmn) (projected_volume_function (m:=m) S) t
  (@theta_star_is_measure R n m hmn)
  (fun p => projected_volume_function_nonnegative S p) ht
  (@theta_star_projected_volume_measurable R n m hmn S hS)).
Qed.

(** Source for [integral_geometric_gauge_nonnegative]:
    supporting nonnegativity of the gauge defined
    in Federer 2.10.5, p. 172. *)
Lemma integral_geometric_gauge_nonnegative (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) (ht : 1<=t)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_suslin_set R S -> 0<=@integral_geometric_gauge R n m hmn t S.
Proof.
move=> hS; rewrite /integral_geometric_gauge; apply: mule_ge0.
- rewrite lee_fin invr_ge0; exact: ltW (@projection_beta_positive R n m hmn t ht).
- exact: (@nonnegative_extended_exponent_norm_ge0 R _
    (@orthogonal_projection_probability R n m hmn) (projected_volume_function (m:=m) S) t
    (@theta_star_is_measure R n m hmn)
    (fun p => projected_volume_function_nonnegative S p) ht
    (@theta_star_projected_volume_measurable R n m hmn S hS)).
Qed.
