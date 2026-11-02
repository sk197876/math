(** Federer (1969), 3.2.38, pp. 274--275: the upper
    Minkowski content of the actual compact image is at most
    the actual source-degree Jacobian integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanJacobianMeasurable EuclideanBoundedJacobianRepresentative
  JacobianDensityMeasure EuclideanJacobianFiniteMass CompactImageMinkowskiRadiusBound
  PositiveRadiusLimits PositiveRadiusReciprocalErrorBound ZeroSourceMinkowskiImage MinkowskiContents
  LipschitzUP MeasureUP MeasureBasic MeasureSubsetIntegral TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_lipschitz_image_upper_minkowski]: Federer
    3.2.38, p. 274: a global Lipschitz map from R^m to
    R^n, m<=n, and compact original C satisfy the upper-content
    Jacobian bound. All natural dimensions, singular maps and
    empty compact sources remain. Dimension zero is the proved
    positive-atom counting identity. For positive dimension the
    actual finite grids and full Steiner polynomial precede the
    full positive-real-radius limsup and reciprocal-error squeeze.
    Lusin 2.3.5 replaces the printed mean selection; the missing
    j=0 Steiner term on p. 275 is retained. Neither change
    adds a hypothesis to this numbered theorem. *)
Theorem compact_lipschitz_image_upper_minkowski (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (C:set (inner_metric_space (@euclidean_inner_productP R m))):
  (m<=n)%N ->is_metric_lipschitz setT f ->compact C ->
  (upper_minkowski_content m (f @` C)<=euclidean_jacobian_measure f C)%E.
Proof.
case:m f C=>[|m] f C hmn hLip hC.
- have hCm:measure_measurable (@euclidean_lebesgue_measure R 0) C.
    apply:euclidean_borel_measurable.
    exact:closed_borel_set (compact_closed (@metric_hausdorff R
      (inner_metric_space (@euclidean_inner_productP R 0))) hC).
  by rewrite (zero_source_minkowski_image_jacobian_identity hLip hCm).
- pose X:=inner_metric_space (@euclidean_inner_productP R m.+1).
  pose mu:=@euclidean_lebesgue_measure R m.+1.
  pose nu:=euclidean_jacobian_measure f.
  have hCm:measure_measurable mu C.
    apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) hC).
  have hn:=euclidean_jacobian_measure_is_measure hLip.
  have hFinite:(nu C< +oo)%E.
    exact:euclidean_jacobian_finite_source_mass hLip hCm (euclidean_compact_finite hC).
  have hFin:nu C \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hn C)).
  pose p:=fine (nu C).
  have hValue:nu C=p%:E by rewrite /p fineK.
  rewrite /nu in hValue.
  have [L [hL hBound]]:=hLip.
  have [J [hBorel [hJ hActual]]]:=
    @euclidean_bounded_top_jacobian_borel_representative R m.+1 n f L (ltW hL) hBound.
  have hDims:(0<m.+1<=n)%N by rewrite ltn0Sn.
  have [K [hK hRadius]]:=@compact_image_minkowski_radius_bound R m.+1 n f J C L
    hDims hC hBound hLip hBorel hJ hActual.
  rewrite hValue.
  apply:(@positive_radius_upper_from_reciprocal_errors R
    (fun r=>minkowski_tube_quotient m.+1 (f @` C) r) p K hK)=>v hv.
  have [d [hd hAll]]:=hRadius v hv.
  exists d; split=>// r hr; have h:=hAll r hr.
  by rewrite hValue in h.
Qed.

(** Source for [federer_3_2_38]: the
    actual displayed subset integral in Federer 3.2.38,
    p. 274. The witness is the existing sealed Jacobian
    density measure, with its original partial integrand domain.
    Finiteness follows from compact source mass, rather than an
    extra finite-integral or derivative-field premise. *)
Theorem federer_3_2_38 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (C:set (inner_metric_space (@euclidean_inner_productP R m))):
  (m<=n)%N ->is_metric_lipschitz setT f ->compact C ->
  exists I : \bar R,
    is_measure_subset_integral (@euclidean_lebesgue_measure R m) C (extended_euclidean_jacobian f) I /\
    (upper_minkowski_content m (f @` C)<=I< +oo)%E.
Proof.
move=>hmn hLip hC.
have hCm:measure_measurable (@euclidean_lebesgue_measure R m) C.
  apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R
    (inner_metric_space (@euclidean_inner_productP R m))) hC).
exists (euclidean_jacobian_measure f C); split.
- exact:euclidean_jacobian_measure_integral hLip hCm.
- apply/andP; split; first exact:compact_lipschitz_image_upper_minkowski hmn hLip hC.
  exact:euclidean_jacobian_finite_source_mass hLip hCm (euclidean_compact_finite hC).
Qed.
