(** Federer (1969), 3.1.2, p. 212: affine examples and the punctured-domain
    boundary. These consequences check the exact definition without
    imposing openness on a domain of full Lebesgue measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric InnerNorm EuclideanLebesgueDimensions
  EuclideanClosedBallVolume EuclideanNoncenteredVitali MetricClosedBalls
  RealNormUP RealMetricBackground MeasureUP MeasureAlmostBasic PartialFunctionUP
  MeasureApproximateLimitUP MeasureSetDensity ApproximateLimitEmptyDomain
  CenteredNullSetDensity EuclideanApproximateContext ApproximateDifferentialUP
  ApproximateDifferentialRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_singleton_null]: supporting the
    punctured approximate quotient of Federer 3.1.2, p. 212. In every
    positive dimension a singleton has zero Lebesgue measure, by the
    proved closed-ball volume at radius zero. *)
Lemma positive_euclidean_singleton_null (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) :
  euclidean_lebesgue_measure n.+1 [set a]=0%E.
Proof.
have he : metric_closed_ball a 0=[set a].
  apply/seteqP; split=> x.
  - move=> hx; have h0 : inner_norm (@euclidean_inner_productP R n.+1) (a-x)=0.
      apply/eqP; rewrite eq_le inner_norm_nonnegative andbT.
      by move: hx; rewrite /metric_closed_ball /= inner_metric_distanceE.
    move/eqP: h0; by rewrite inner_norm_eq0 subr_eq0=> /eqP.
  - move=> <-; by rewrite /metric_closed_ball /= mdistxx.
rewrite -he euclidean_closed_ball_normalized_volume // exprS mul0r mulr0.
reflexivity.
Qed.

(** Source for [approximate_differential_affine_conull]: affine case
    of the definition in Federer 3.1.2, p. 212. A domain with null
    complement need not be open; on that actual domain the affine map
    has approximate differential L at every domain point. *)
Theorem approximate_differential_affine_conull (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n.+1 -> Prop)
    (f : R_n R n.+1 -> Y) (L : Hom (R_n R n.+1) Y) (c : Y) a :
  euclidean_lebesgue_measure n.+1 (~` A)=0%E ->
  (forall x, A x -> f x=L x+c) -> A a ->
  has_approximate_differential NY A f a L.
Proof.
move=> hA hf ha; split=> //.
pose N : set (inner_metric_space (@euclidean_inner_productP R n.+1)) := (~` A) `|` [set a].
have hN : euclidean_lebesgue_measure n.+1 N=0%E.
  exact: (@measure_null_union R _ (@euclidean_lebesgue_measure R n.+1)
    (euclidean_lebesgue_is_measure R n.+1) (~` A) [set a] hA
    (@positive_euclidean_singleton_null R n a)).
apply: (@centered_almost_constant_approximate_limit R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)]
  [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R n.+1)
  (approximate_remainder_quotient NY A f a L) N a 0
  (euclidean_lebesgue_is_measure R n.+1) _ hN).
- move=> x r hr; split; first exact: euclidean_closed_ball_positive.
  by rewrite euclidean_closed_ball_normalized_volume ?ltW // fin_numE.
- move=> x hn.
  have hx : A x by apply: contrapT=> hx; apply: hn; left.
  have hxa : x!=a by apply/eqP=> h; apply: hn; right; exact h.
  apply: (@approximate_remainder_quotient_graph R n.+1 Y NY A f a L x 0).2.
  split=> //; split=> //.
  rewrite (hf x hx) (hf a ha) linearB /=.
  have hi : L x+c-(L a+c)-(L x-L a)=0.
    by rewrite (addrC (L a) c) opprD addrA addrK subrr.
  by rewrite hi (real_seminorm_zero hNY.1) mul0r.
Qed.

(** Source for [zero_dimensional_no_approximate_differential]: explicit
    dimension-zero boundary of the punctured limit in Federer 3.1.2,
    p. 212. Under the project's unit-mass empty-product convention,
    the punctured quotient has empty domain, so no approximate limit
    exists. This is a convention consequence, not a printed assertion. *)
Theorem zero_dimensional_no_approximate_differential (R : realType) (Y : lmodType R)
    (NY : Y -> R) (A : R_n R 0 -> Prop) (f : R_n R 0 -> Y)
    a (L : Hom (R_n R 0) Y) :
  ~ has_approximate_differential NY A f a L.
Proof.
move=> [_ hl]; have hd := approximate_limit_domain_density hl.
have he : partial_function_domain (approximate_remainder_quotient NY A f a L)=set0.
  apply/seteqP; split=> x; last by move=> [].
  move=> [q hq]; have [_ [hn _]] := (@approximate_remainder_quotient_graph R 0 Y NY A f a L x q).1 hq.
  by rewrite (coordinate_zero x) (coordinate_zero a) eqxx in hn.
rewrite he setC0 in hd.
exact: whole_set_density_not_zero (euclidean_approximate_context R 0) hd.
Qed.
