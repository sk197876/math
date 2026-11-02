(** Federer (1969), 2.10.27, p. 191: supporting abstract specification of
    the nonnegative ball-section cost profile alpha(k)(r^2-|y-u|^2)^(k/2) on
    the closed first-coordinate ball, and zero outside. Specify this
    auxiliary function by its values; an auxiliary Euclidean volume
    construction will prove existence and the displayed integral identity.
    The boundary is retained under the project's k=0 convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_euclidean_ball_section_profile]: supporting
    abstract value laws for the ball-section integrand
    in 2.10.27, p. 191. The printed open
    projection is corrected to its closed counterpart;
    this does not alter positive-dimensional outer integrals. *)
Record is_euclidean_ball_section_profile (R : realType) (m k : nat)
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R)
    (q : inner_metric_space (@euclidean_inner_productP R m) -> \bar R) : Prop := {
  (** Source for [ball_section_profile_inside]: supporting
      section cost alpha(k) times the kth power
      of the section radius in 2.10.27, p. 191.
      Integer powers of the nonnegative square root
      avoid introducing a new real-power convention. *)
  ball_section_profile_inside : forall y, (mdist u y<=r)%R ->
    q y=(euclidean_unit_ball_volume R k*Num.sqrt (r^+2-mdist u y^+2)^+k)%R%:E;
  (** Source for [ball_section_profile_outside]: supporting
      zero cost for empty sections outside the closed
      first-coordinate ball in 2.10.27, pp. 190–191. *)
  ball_section_profile_outside : forall y, (r<mdist u y)%R -> q y=0
}.

(** Source for [ball_section_profile_unique]: supporting
    uniqueness of the auxiliary profile used in
    2.10.27, p. 191, by its inside/outside
    laws. This is not an extra claim in the book. *)
Lemma ball_section_profile_unique (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R)
    (p q : inner_metric_space (@euclidean_inner_productP R m) -> \bar R) :
  is_euclidean_ball_section_profile k u r p -> is_euclidean_ball_section_profile k u r q -> p=q.
Proof.
move=> hp hq; apply: funext=> y; case: (leP (mdist u y) r)=> hy.
- by rewrite (ball_section_profile_inside hp hy) (ball_section_profile_inside hq hy).
- by rewrite (ball_section_profile_outside hp hy) (ball_section_profile_outside hq hy).
Qed.

(** Source for [ball_section_profile_nonnegative]: supporting
    nonnegative summands in the covering proof of
    2.10.27, p. 191. It follows from the
    value specification alone, including radius and degree zero. *)
Lemma ball_section_profile_nonnegative (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R)
    (q : inner_metric_space (@euclidean_inner_productP R m) -> \bar R) :
  is_euclidean_ball_section_profile k u r q -> forall y, 0<=q y.
Proof.
move=> hq y; case: (leP (mdist u y) r)=> hy.
- rewrite (ball_section_profile_inside hq hy) lee_fin; apply: mulr_ge0.
  + exact: ltW (euclidean_unit_ball_volumeE R k).2.
  + exact: exprn_ge0 (sqrtr_ge0 _).
- by rewrite (ball_section_profile_outside hq hy).
Qed.
