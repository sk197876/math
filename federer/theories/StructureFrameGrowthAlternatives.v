(** Federer (1969), 3.3.4, p. 289: the original coordinate
    alternatives imply the actual plane-growth alternatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  OrthogonalMaps EuclideanProjectionSpace EuclideanBlockLinearMaps
  StructureCone StructureCoordinateCones StructureCoordinateGrowth StructureCoordinateGrowthLaws
  StructureCoordinateAlternatives StructurePlaneGrowth StructureProjectionKernel
  StructureConeCoordinateGrowthBounds StructureCoordinateApertureMonotonic
  StructureApertureEnlargement StructureZeroLimitComparison StructureInfiniteLimitComparison
  StructureFiniteZeroLimits StructureConeDensityValues PositiveRightOrderLimit
  FinitePositiveRadiusCutoff MeasureUP MeasureBasic ExtendedRealBounds
  SignedSquareRootSealed SignedSquareRootLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Frame.
Variable R:realType.
Variables m k:nat.
Hypothesis hmn:(m<=m+k)%N.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R (m+k))).
Variables (phi:set E->\bar R) (A:set E) (a:E).
Variable f:{linear R_n R (m+k)->R_n R (m+k)}.
Variable p:euclidean_projection_space R (m+k) m.
Hypothesis hPhi:is_measure phi.
Hypothesis hF:is_orthogonal_map (@euclidean_inner_product R (m+k))
  (@euclidean_inner_product R (m+k)) f.
Hypothesis hP:forall y,euclidean_projection_linear p y=@euclidean_first_block R m k (f y).
Hypothesis hk:(0<k)%N.
Local Notation V:=(structure_projection_kernel hmn p).

(** Source for [structure_plane_radius_supremum_nonnegative]: the
    radius supremum in Federer 3.3.4, p. 288, is nonnegative at every
    positive cutoff and aperture. A positive half-cutoff radius provides
    an actual value, so no empty supremum is silently used. *)
Lemma structure_plane_radius_supremum_nonnegative (delta s:R):
  0<delta ->0<s ->(0<=structure_plane_radial_supremum m phi A a V delta s)%E.
Proof.
move=>hd hs; have hr:=structure_density_positive_half_bounds hd.
apply:le_trans _ (extended_real_sup_upper (ex_intro _ (delta/2) (conj hr erefl))).
apply:mule_ge0; last by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
apply:mule_ge0; first exact:measure_nonnegative hPhi _.
by rewrite lee_fin exprn_ge0 // invr_ge0 ltW //; exact:(andP hr).1.
Qed.

(** Source for [structure_frame_zero_growth]: Federer 3.3.4, p. 289,
    intersection_j B_j is contained in B. A finite common positive
    radial cutoff retains every original coordinate zero limit. Exact
    finite subadditivity, the proved u(s)<=sqrt(k)s bound and finite
    aperture scaling give the ordinary zero limit of the original cone. *)
Theorem structure_frame_zero_growth:
  (forall j:'I_k,structure_coordinate_zero_growth phi A a f j) ->
  structure_plane_zero_growth m phi A a V.
Proof.
move=>hB.
have hEach j:exists d:R,0<d /\forall eta:R,0<eta<d ->
    positive_right_extended_order_limit (structure_coordinate_radial_supremum phi A a f j eta) 0%E.
  have [d [hd hLimit]]:=hB j.
  exists d; split=>// eta /andP [he hSmall].
  exact:(@structure_coordinate_zero_smaller_cutoff R m k phi A a f j eta d hPhi he (ltW hSmall) hLimit).
have [d [hd hCommon]]:=@finite_common_positive_radius_bound R [the finType of 'I_k]
  (fun j eta=>positive_right_extended_order_limit
    (structure_coordinate_radial_supremum phi A a f j eta) 0%E) hEach.
pose delta:=d/2.
have hDelta:0<delta<d:=structure_density_positive_half_bounds hd.
pose c:=@SignedSquareRoot.value R (k%:R).
have hc0:0<=c:=(signed_root_sign_bounds (k%:R:R)).1 (ltac:(by rewrite ler0n)).
have hk0:0<=(k%:R:R) by rewrite ler0n.
have hcSquare:c^+2=(k%:R:R) by rewrite /c signed_root_square (ger0_norm hk0).
have hkR:0<(k%:R:R) by rewrite ltr0n.
have hc:0<c by nra.
have hcp:0<c^+m by rewrite exprn_gt0.
exists delta; split; first exact:(andP hDelta).1.
apply:(@structure_zero_limit_scaled_comparison R
  (structure_plane_radial_supremum m phi A a V delta)
  (fun s=>\sum_j structure_coordinate_radial_supremum phi A a f j delta s)
  c (c^+m) 1 hc hcp ltr01).
- move=>s hs; exact:structure_plane_radius_supremum_nonnegative (andP hDelta).1 hs.
- move=>s hs.
  apply:(@structure_plane_coordinate_upper_growth R m k ((m+k)-m) phi A a V f hPhi delta s c
    (andP hs).1 hc)=>r hr.
  exact:(@structure_frame_cone_linear_enlargement R m k hmn A a f p r%:E s hF hP hk hs).
- apply:structure_finite_nonnegative_zero_limits.
  + move=>j s hs; exact:(@structure_coordinate_supremum_nonnegative R m k phi A a f j delta s hPhi (andP hDelta).1 hs).
  + exact:hCommon delta hDelta.
Qed.

(** Source for [structure_frame_infinite_growth]: Federer 3.3.4,
    p. 289, union_j C_j is contained in C. The original one-coordinate
    cone is contained in the original plane cone at every sufficiently
    small positive aperture; its infinite upper growth forces the plane
    upper growth at every positive radial cutoff. *)
Theorem structure_frame_infinite_growth (j:'I_k):
  structure_coordinate_infinite_growth phi A a f j ->
  structure_plane_infinite_growth m phi A a V.
Proof.
move=>hC delta hd.
apply:(@structure_infinite_limit_scaled_comparison R
  (structure_coordinate_radial_supremum phi A a f j delta)
  (structure_plane_radial_supremum m phi A a V delta) 1 1 1 ltr01 ltr01 ltr01); last exact:hC delta hd.
move=>s hs; rewrite mul1r mul1e.
apply:(@structure_plane_coordinate_lower_growth R m k ((m+k)-m) phi A a V f hPhi j delta s (andP hs).1)=>r hr.
have [u hU]:=structure_enlarged_aperture_exists hk hs.
have hInclude:=(structure_frame_cone_union_squeeze hmn A a r%:E hF hP hk hs hU).1.
move=>x hx; apply:hInclude; by exists j.
Qed.
End Frame.
