(** Federer 2.10.27, p. 191: the original ball-section cost
    profile in every nonnegative real section degree. Specify its
    exact pointwise values before selecting a value or proving its
    integral. The Euclidean base dimension remains a natural number. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealPower RealHausdorffBallCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_real_euclidean_ball_section_profile]: the exact
    alpha(k) times the k-th real power of the section radius in
    the first display of Federer 2.10.27, p. 191. Its integral
    is not an assumption. Keep the closed projection boundary,
    including the degree-zero convention and zero-radius sections. *)
Record is_real_euclidean_ball_section_profile (R:realType) m (k:R)
    (hk:(0<=k)%R) (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R)
    (q:inner_metric_space (@euclidean_inner_productP R m)->\bar R):Prop:={
  (** Source for [real_ball_section_profile_inside]: the original
      section cost on the closed first-coordinate ball in Federer
      2.10.27, p. 191, with the actual Gamma-defined alpha(k). *)
  real_ball_section_profile_inside:forall y,(mdist u y<=r)%R ->
    q y=(real_hausdorff_ball_coefficient hk*
      real_power (Num.sqrt (r^+2-mdist u y^+2)) k)%R%:E;
  (** Source for [real_ball_section_profile_outside]: the empty
      section outside the closed projected ball has cost zero,
      as used in Federer 2.10.27, p. 191. *)
  real_ball_section_profile_outside:forall y,(r<mdist u y)%R ->q y=0
}.

(** Source for [real_ball_section_profile_unique]: supporting
    uniqueness of the real-degree profile of Federer 2.10.27,
    p. 191, from its independently specified inside and outside
    values. No integrability or measurability is assumed. *)
Lemma real_ball_section_profile_unique (R:realType) m (k:R) (hk:(0<=k)%R)
    (u:inner_metric_space (@euclidean_inner_productP R m)) r p q:
  is_real_euclidean_ball_section_profile hk u r p ->
  is_real_euclidean_ball_section_profile hk u r q ->p=q.
Proof.
move=> hp hq;apply:funext=>y;case:(leP (mdist u y) r)=>hy.
- by rewrite (real_ball_section_profile_inside hp hy) (real_ball_section_profile_inside hq hy).
- by rewrite (real_ball_section_profile_outside hp hy) (real_ball_section_profile_outside hq hy).
Qed.

(** Source for [real_ball_section_profile_nonnegative]: supporting
    sign law in the covering sum of Federer 2.10.27, p. 191.
    Actual Gamma positivity and the earlier real-power sign law
    suffice, including both zero endpoints. *)
Lemma real_ball_section_profile_nonnegative (R:realType) m (k:R) (hk:(0<=k)%R)
    (u:inner_metric_space (@euclidean_inner_productP R m)) r q:
  is_real_euclidean_ball_section_profile hk u r q ->forall y,0<=q y.
Proof.
move=> hq y;case:(leP (mdist u y) r)=>hy.
- rewrite (real_ball_section_profile_inside hq hy) lee_fin.
  exact:mulr_ge0 (ltW (real_hausdorff_ball_coefficient_positive hk)) (real_power_nonnegative _ _).
- by rewrite (real_ball_section_profile_outside hq hy).
Qed.
