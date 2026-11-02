(** Federer (1969), 2.10.5, p. 173, last paragraph, paraphrased: I_t(A)=0
    exactly when A is contained in a Borel B whose projected m-volume is
    zero for theta-star almost every projection. Thus all exponents have the
    same null sets. The proof uses an actual Borel hull, the incidence outer
    measure and Fubini, normalized-measure monotonicity, and small zero-cost
    Borel covers. Infinite projection volumes are retained throughout. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  OrthogonalProjectionProbability ProjectedVolumeMeasurability ProjectionBeta
  IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricExponentMonotone
  IntegralGeometricNullCover ProjectionIncidenceMeasure NonnegativeExtendedExponentNorm
  NonnegativeExtendedNormZero MeasureUP MeasureBasic MeasureAlmostUP
  BorelRegularMeasureUP TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_one_null_projection_hull]:
    supporting exponent-one forward implication in
    Federer 2.10.5, p. 173. Its actual Borel
    hull has zero incidence measure; Fubini and
    the zero-norm criterion give the required
    almost everywhere zero projected volumes. *)
Lemma integral_geometric_one_null_projection_hull (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @integral_geometric_measure R n m hmn 1 A=0 ->
  exists B, A `<=` B /\ borel_set B /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p | projected_volume_function (m:=m) B p=0].
Proof.
move=> hA.
have [B [hAB [hB heB]]] := borel_regular_cover
  (@integral_geometric_measure_borel_regular R n m hmn 1 (lexx 1)) A.
exists B; split=> //; split=> //.
have hzero : @projected_incidence_measure R n m hmn B=0.
  apply/eqP; rewrite eq_le (measure_nonnegative (@projected_incidence_is_measure R n m hmn) B) andbT.
  have hb := @projected_incidence_integral_geometric_bound R n m hmn B.
  by rewrite -heB hA mule0 in hb.
have hnorm : nonnegative_extended_exponent_norm (@orthogonal_projection_probability R n m hmn)
    (projected_volume_function (m:=m) B) 1=0.
  rewrite -(@integral_geometric_gauge_normalized R n m hmn 1 (lexx 1) B).
  by rewrite (@integral_geometric_one_gauge_incidence R n m hmn B (metric_borel_suslin hB)).
exact: (@nonnegative_extended_norm_zero_iff R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_function (m:=m) B) 1
  (fun p => projected_volume_function_nonnegative B p) (lexx 1)
  (@theta_star_projected_volume_measurable R n m hmn B (metric_borel_suslin hB))).1 hnorm.
Qed.

(** Source for [integral_geometric_projection_null_iff]:
    direct Borel projection-null characterization
    in Federer 2.10.5, p. 173. The target
    A is arbitrary and the exponent includes
    infinity. The Borel superset is produced,
    not supplied as an additional hypothesis. *)
Theorem integral_geometric_projection_null_iff (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t ->
  (@integral_geometric_measure R n m hmn t A=0 <->
   exists B, A `<=` B /\ borel_set B /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p | projected_volume_function (m:=m) B p=0]).
Proof.
move=> ht; split.
- move=> hz; apply: integral_geometric_one_null_projection_hull.
  have hb := @projection_beta_positive R n m hmn 1 (lexx 1).
  have hbN : (@projection_beta R n m hmn 1!=0)%R by rewrite gt_eqF.
  have hbound := @integral_geometric_normalized_measure_monotone R n m hmn 1 t A (lexx 1) ht.
  rewrite hz mule0 in hbound.
  have he : (@projection_beta R n m hmn 1)%:E * @integral_geometric_measure R n m hmn 1 A=0.
    apply/eqP; rewrite eq_le hbound /=; apply: mule_ge0.
    - rewrite lee_fin; exact: ltW hb.
    - exact: measure_nonnegative (@integral_geometric_measure_is_measure R n m hmn 1 (lexx 1)) A.
  have hcancel := congr1 (fun z => (@projection_beta R n m hmn 1)^-1%R%:E*z) he.
  by rewrite muleA -EFinM mulVf // mul1e mule0 in hcancel.
- move=> [B [hAB [hB hz]]].
  apply/eqP; rewrite eq_le (measure_nonnegative
    (@integral_geometric_measure_is_measure R n m hmn t ht) A) andbT.
  have hmono := measure_mono (@integral_geometric_measure_is_measure R n m hmn t ht) hAB.
  by rewrite (@integral_geometric_borel_projection_null R n m hmn B t hB ht hz) in hmono.
Qed.

(** Source for [integral_geometric_common_null_sets]:
    direct final assertion of Federer 2.10.5,
    p. 173: the measures I_t, for all
    1<=t<=infinity, have the same null sets.
    Both finite and infinite exponents are included. *)
Corollary integral_geometric_common_null_sets (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (s t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=s -> 1<=t ->
  (@integral_geometric_measure R n m hmn s A=0 <->
   @integral_geometric_measure R n m hmn t A=0).
Proof.
move=> hs ht.
exact: iff_trans (@integral_geometric_projection_null_iff R n m hmn s A hs)
  (iff_sym (@integral_geometric_projection_null_iff R n m hmn t A ht)).
Qed.
