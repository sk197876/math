(** Public projected-volume gauge for Federer (1969), 2.10.4, p. 172. Use
    only the abstract laws of the sealed general extended-real supremum and
    the existing Euclidean Lebesgue and projection interfaces. Source
    context and degree scope: ProjectedVolumeGaugeUP.v. No new existence
    axiom or external geometric measure is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FiniteCoordinates CoordinateProjection OrthogonalEuclidean Adjoint AdjointUP
  BasisInterpolation OrthogonalBasisCriteria OrthonormalFamilies EuclideanLebesgueDimensions
  ProjectedVolumeGaugeUP ExtendedRealBoundsUP ExtendedRealBounds ExtendedRealBoundsSealed
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport BorelCoverCostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_projection_exists]: supporting
    nonemptiness of O*(n,m) in Federer 2.10.4,
    p. 172, under m<=n. Use the adjoint of
    the coordinate isometric injection, as in 1.7.4,
    pp. 30–31; m=0 is also permitted here. *)
Lemma euclidean_projection_exists (R : realType) (n m : nat) :
  (m<=n)%N -> exists p : {linear R_n R n -> R_n R m}, O_star p.
Proof.
move=> hmn.
pose e (i : 'I_m) : R_n R n := @coordinate_basis R n (widen_ord hmn i).
have hw i j : (widen_ord hmn i==widen_ord hmn j)=(i==j).
  by apply/eqP/eqP=> [h|->] //; apply: val_inj; exact: (congr1 val h).
have he : orthonormal_family (@euclidean_inner_product R n) e.
  move=> i j; rewrite /e euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite hw eq_sym.
pose f := basis_interpolation (@coordinate_basisP R m) e.
have hf : @FedererOrthogonal.O R n m f.
  apply: (@orthogonal_map_basis_criterion R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m)).
  - by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
  - by move=> i j; rewrite /f !basis_interpolationE he.
exists (inner_adjoint (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R m) f).
exists f; split=> //; exact: inner_adjointP.
Qed.

(** Source for [projected_volume_gauge]: direct selected
    supremum in Federer 2.10.4, p. 172, using
    the previously sealed extended-real bound operator.
    Mathematical results below retain m<=n when that
    hypothesis is needed for nonnegativity. *)
Definition projected_volume_gauge (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :=
  extended_real_sup (projected_volume_values m A).

(** Source for [projected_volume_gauge_specification]:
    proved supremum laws for the gauge of Federer
    2.10.4, p. 172, without an implementation-
    dependent formula or an assumed maximizing projection. *)
Lemma projected_volume_gauge_specification (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_projected_volume_gauge m A (projected_volume_gauge m A).
Proof. exact: ExtendedRealBounds.laws. Qed.

(** Source for [projected_volume_gauge_projection_bound]:
    supporting upper-bound clause for every projection
    in the display of Federer 2.10.4, p. 172. *)
Lemma projected_volume_gauge_projection_bound (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : {linear R_n R n -> R_n R m}) : O_star p ->
  euclidean_lebesgue_measure m (p @` A)<=projected_volume_gauge m A.
Proof.
move=> hp; apply: extended_real_sup_upper; exists p; by split.
Qed.

(** Source for [projected_volume_gauge_least_bound]:
    supporting least-bound clause of the supremum in
    Federer 2.10.4, p. 172; finite values and
    infinity use the same order laws. *)
Lemma projected_volume_gauge_least_bound (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (b : \bar R) :
  (forall p : {linear R_n R n -> R_n R m}, O_star p ->
    euclidean_lebesgue_measure m (p @` A)<=b) -> projected_volume_gauge m A<=b.
Proof. move=> hb; apply: extended_real_sup_least=> v [p [hp ->]]; exact: hb. Qed.

(** Source for [projected_volume_gauge_nonnegative]:
    supporting nonnegative cost for Federer 2.10.4,
    p. 172. The dimensional premise makes O* nonempty;
    Lebesgue nonnegativity then gives a nonnegative member
    below the supremum, without adjoining an extra value. *)
Lemma projected_volume_gauge_nonnegative (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (m<=n)%N -> 0<=projected_volume_gauge m A.
Proof.
move=> hmn; have [p hp] := @euclidean_projection_exists R n m hmn.
exact: le_trans (measure_nonnegative (euclidean_lebesgue_is_measure R m) _)
  (projected_volume_gauge_projection_bound A hp).
Qed.

(** Source for [projected_volume_gauge_mono]: supporting
    inclusion monotonicity for the projected-volume cost
    in Federer 2.10.4, p. 172. No Borel or
    convex assumption on the two input sets is needed. *)
Lemma projected_volume_gauge_mono (R : realType) (n m : nat)
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) :
  A `<=` B -> projected_volume_gauge m A<=projected_volume_gauge m B.
Proof.
move=> hAB; apply: projected_volume_gauge_least_bound=> p hp.
apply: le_trans _ (projected_volume_gauge_projection_bound B hp).
apply: (measure_mono (euclidean_lebesgue_is_measure R m))=> y [x hx <-].
exists x=> //; exact: hAB.
Qed.

(** Source for [projected_volume_gauge_empty]: supporting
    empty-generator convention for the Borel family in
    Federer 2.10.4(1), p. 172. Its projected
    Lebesgue volumes are all zero when m<=n. *)
Lemma projected_volume_gauge_empty (R : realType) (n m : nat) :
  (m<=n)%N -> @projected_volume_gauge R n m set0=0.
Proof.
move=> hmn; apply/eqP; rewrite eq_le (projected_volume_gauge_nonnegative set0 hmn) andbT.
apply: projected_volume_gauge_least_bound=> p hp.
by rewrite image_set0 (measure_empty (euclidean_lebesgue_is_measure R m)).
Qed.

(** Source for [projected_volume_gauge_countable_cover]:
    supporting covering inequality of the cost in
    Federer 2.10.4, p. 172, using 2.1.2,
    p. 53. Each projected image is covered by the
    corresponding projected family; compare its countable
    sum to the sum of the separate suprema. *)
Theorem projected_volume_gauge_countable_cover (R : realType) (n m : nat)
    (J : choiceType) (D : set J)
    (S : J -> set (inner_metric_space (@euclidean_inner_productP R n))) A :
  countable D -> A `<=` \bigcup_(j in D) S j ->
  projected_volume_gauge m A<=nonnegative_sum D (fun j => projected_volume_gauge m (S j)).
Proof.
move=> hD hcover; apply: projected_volume_gauge_least_bound=> p hp.
have hcov : p @` A `<=` \bigcup_(j in D) (p @` S j).
  move=> y [x hx <-]; have [j hj hs] := hcover x hx; exists j=> //; by exists x.
apply: le_trans (measure_indexed_cover (euclidean_lebesgue_is_measure R m) hD hcov) _.
apply: nonnegative_sum_mono=> j hj; exact: projected_volume_gauge_projection_bound.
Qed.

(** Source for [projected_volume_gauge_borel_cover_cost]:
    supporting specialization of the covering law to
    Borel generators in Federer 2.10.4(1), p. 172.
    The dimensional premise is the printed one; no
    measurability of individual projection images is assumed. *)
Theorem projected_volume_gauge_borel_cover_cost (R : realType) (n m : nat) :
  (m<=n)%N -> is_borel_cover_cost (@projected_volume_gauge R n m).
Proof.
move=> hmn; split.
- move=> A hA; exact: projected_volume_gauge_nonnegative.
- move=> J D S A hD hA hS hcov; exact: projected_volume_gauge_countable_cover hD hcov.
Qed.
