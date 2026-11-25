(** Federer (1969), 4.1.27, p. 384:
    the source is the actual Euclidean
    current restricted to the original open
    unit cube. Its compact support and
    flatness follow from the earlier bounded
    characteristic-current results, retaining the nonzero
    zero-dimensional cube. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness EuclideanCoordinateLoneBound
  EuclideanOpenUnitCube EuclideanUnitCubeBorel EuclideanLebesgueDimensions
  CoveringFamilyUP CoveringFamilyLaws MetricClosedBalls MetricBoundedClosureLaws
  BorelRegularMeasureUP TopologicalBorel MeasureUP CurrentSpaces CurrentSupportGeometry
  SmoothCompactSet EuclideanCharacteristicCurrent CurrentCharacteristicSupportClosure
  CurrentBoundedCharacteristicFlat FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_source_measurable]: the original
    open cube in 4.1.27, p. 384,
    is Lebesgue measurable by the already
    proved Borel regularity of L^m. *)
Lemma simplex_cube_source_measurable (R:realType) m:
  measure_measurable (@euclidean_lebesgue_measure R m) (@euclidean_open_unit_cube R m).
Proof.
exact:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R m)
  (euclidean_lebesgue_borel_regular R m) (@euclidean_open_unit_cube_borel R m)).
Qed.

(** Source for [simplex_cube_source_bounded]: the original
    cube carrier is bounded, supporting its
    compact-current image in 4.1.27, p. 384.
    The coordinate norm bound applies also
    when there are no coordinates. *)
Lemma simplex_cube_source_bounded (R:realType) m:
  @metric_set_bounded R (inner_metric_space (@euclidean_inner_productP R m))
    (@euclidean_open_unit_cube R m).
Proof.
pose IT:=inner_metric_space (@euclidean_inner_productP R m).
pose r:R:=m%:R.
have hBall:@metric_set_bounded R IT (metric_closed_ball (0:IT) r).
  apply:covering_closed_ball_bounded;by rewrite /r ler0n.
apply:(@metric_bounded_subset R IT (@euclidean_open_unit_cube R m)
  (metric_closed_ball (0:IT) r) _ hBall).
move=>x hX.
change (is_true (mdist (0:IT) x<=r)).
rewrite metric_sym inner_metric_distanceE subr0.
apply:(le_trans (@euclidean_coordinate_lone_bound R m x)).
have hCoordinates:forall i,`|x i|<=1.
  move=>i;rewrite (ger0_norm (ltW (andP (hX i)).1));exact:ltW (andP (hX i)).2.
have hSum: (\sum_(i:'I_m) `|x i|)<=\sum_(i:'I_m) (1:R).
  apply:ler_sum=>i _;exact:hCoordinates.
by rewrite sumr_const card_ord in hSum.
Qed.

(** Source for [simplex_cube_source_current]: the literal
    E^m restricted to C in the
    current-image assertion of 4.1.27, p. 384.
    This is an abbreviation of the
    existing characteristic current, not a new
    selected integration functional. *)
Definition simplex_cube_source_current (R:realType) (h2:(1+1:R)!=0) m:=
  @euclidean_characteristic_current R h2 m (@euclidean_open_unit_cube R m)
    (@simplex_cube_source_measurable R m).

(** Source for [simplex_cube_source_closure_compact]: the closure
    of the original cube in 4.1.27,
    p. 384, is compact by the
    earlier Euclidean bounded-closure theorem. This
    includes the one-point cube at m=0. *)
Lemma simplex_cube_source_closure_compact (R:realType) m:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (@closure (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) (@euclidean_open_unit_cube R m)).
Proof.
exact:(@euclidean_bounded_closure_compact R m (@euclidean_open_unit_cube R m)
  (@simplex_cube_source_bounded R m)).
Qed.

(** Source for [simplex_cube_source_index]: the original
    closed cube used as a compact
    support index in 4.1.27, p. 384.
    This packages its proved compactness in
    the existing compact-set interface and makes
    no new choice of a carrier. *)
Definition simplex_cube_source_index (R:realType) m:
    smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True):=
  @Build_smooth_compact_set R (R_n R m)
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) (fun _=>True)
    (@closure (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) (@euclidean_open_unit_cube R m))
    (fun _ _=>Logic.I) (@simplex_cube_source_closure_compact R m).

(** Source for [simplex_cube_source_current_compact]: the original
    cube current is compactly supported in
    its closure, supporting the pushforward in
    4.1.27, p. 384. No finite-perimeter
    assumption on a general source set
    enters this bounded-cube specialization. *)
Theorem simplex_cube_source_current_compact (R:realType) (h2:(1+1:R)!=0) m:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (@current_support R h2 m (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R m)) x) m
      (@simplex_cube_source_current R h2 m)).
Proof.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun _:X=>True.
pose hU:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose K:=@simplex_cube_source_index R m.
apply:(@current_support_compact_bound R h2 m m U hU K
  (@simplex_cube_source_current R h2 m)).
exact:(@euclidean_characteristic_current_support_closure R h2 m
  (@euclidean_open_unit_cube R m) (@simplex_cube_source_measurable R m)).
Qed.

(** Source for [simplex_cube_source_current_flat]: the original
    cube current belongs to the actual
    flat union before applying 4.1.25,
    supporting 4.1.27, p. 384. This
    follows from bounded characteristic flatness and
    adds no normality premise. *)
Theorem simplex_cube_source_current_flat (R:realType) (h2:(1+1:R)!=0) m:
  @is_flat_current R h2 m m (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) x)
    (@simplex_cube_source_current R h2 m).
Proof.
exact:(@current_bounded_characteristic_flat R h2 m (@euclidean_open_unit_cube R m)
  (@simplex_cube_source_measurable R m) (@simplex_cube_source_bounded R m)).
Qed.
