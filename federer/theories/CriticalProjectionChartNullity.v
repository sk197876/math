(** Federer (1969), 3.4.2(8), pp. 315–316: assemble
    the actual adapted cube images on the original compact source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  RealNormUP NormMetric OrthogonalMaps OrthogonalFinite NormDifferentialUP
  NormDifferentialLinear NormBoundedLinearTopology NormRegularity NormRegularityLinearMaps
  RelativeClassUP MetricClosedBalls EuclideanProjectionSpace CriticalManifoldFamilyUP
  CriticalChartRetractionClass CriticalAdaptedCoordinates CriticalLocalCube
  CriticalChartCubeNullity CompactLocallyNullImage CriticalOscillation PositiveRightOrderLimit
  MetricRealPowerMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_projection_chart_image_nullity]: the
    last assembly of 3.4.2(8), pp. 315–316. Choose actual
    adapted orthogonal coordinates, take compact contained cubes,
    and pull back their interiors to the original source. The
    compact source has a finite subcover. The actual projection
    image dimension is the only geometric input still explicit
    here; it is proved separately from ker(p) contained in Z. *)
Theorem critical_projection_chart_image_nullity (R:realType) m a b
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m (a+b)) (g:R_n R (a+b)->R_n R m)
    (A:G (R_n R (a+b)) a)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R m->Y)
    (lambda c:R):
  (0<a)%N ->0<lambda ->0<=c ->
  is_critical_manifold_chart 1 Z S p g ->
  (forall y,grassmann_val A y <->exists z,Z z /\euclidean_projection_linear p z=y) ->
  C `<=` S ->@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f 1 ->
  positive_right_extended_order_limit (fun delta=>critical_eta NY Z S C f lambda delta) 0%E ->
  @metric_real_power_measure R (real_norm_metric_space hNY) c
    (b%:R+a%:R/lambda) (f @` C)=0%E.
Proof.
move=>ha hLambda hc hChart hA hCS hC hf hEta.
pose E:=R_n R (a+b).
pose NE:=inner_norm (@euclidean_inner_productP R (a+b)).
pose hNE:=inner_norm_real_norm (@euclidean_inner_productP R (a+b)).
pose NM:=inner_norm (@euclidean_inner_productP R m).
pose hNM:=inner_norm_real_norm (@euclidean_inner_productP R m).
have [H [hH hFirst]]:=critical_adapted_coordinates_exists A (leq_addr b a).
have [J [hHJ [hJH hJ]]]:=@orthogonal_endomorphism_inverse_exists R E _
  (@euclidean_inner_productP R (a+b)) (a+b) (@coordinate_basis R (a+b))
  (@coordinate_basisP R (a+b)) H hH.
have hNormH x:NE (H x)=NE x:=orthogonal_map_norm
  (@euclidean_inner_productP R (a+b)) (@euclidean_inner_productP R (a+b)) hH x.
have hNormJ x:NE (J x)=NE x:=orthogonal_map_norm
  (@euclidean_inner_productP R (a+b)) (@euclidean_inner_productP R (a+b)) hJ x.
have hHBound:norm_bounded_linear NE NE (hom_of_linear H).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite hom_of_linearE hNormH mul1r.
have hJBound:norm_bounded_linear NE NE (hom_of_linear J).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite hom_of_linearE hNormJ mul1r.
pose U:=fun z:E=>(euclidean_projection_linear p @` S) (H z).
pose G:=fun z:E=>g (H z).
have hG:norm_class hNE hNM U G 1:=@norm_class_precompose_linear R E E (R_n R m)
  NE NE NM hNE hNE hNM (euclidean_projection_linear p @` S) g (hom_of_linear H) 1
  hHBound (critical_chart_inverse_class hChart).
pose T:=hom_comp (hom_of_linear J) (hom_of_linear (euclidean_projection_linear p)).
have hTBound:norm_bounded_linear NM NE T:=norm_bounded_linear_compose
  (critical_projection_bounded_linear p) hJBound.
have hTContinuous:=@norm_bounded_linear_continuous R (R_n R m) E NM NE hNM hNE T hTBound.
pose mu:=@metric_real_power_measure R (real_norm_metric_space hNY) c (b%:R+a%:R/lambda).
have hMu:is_measure mu:=@metric_real_power_measure_is_measure R (real_norm_metric_space hNY) c (b%:R+a%:R/lambda) hc.
apply:(@compact_locally_null_image R (real_norm_metric_space hNM)
  [the choiceType of real_norm_metric_space hNY] mu f C hMu hC)=>x hx.
pose z:E:=T x.
have hCoordinate:H z=euclidean_projection_linear p x.
  change (H (J (euclidean_projection_linear p x))=euclidean_projection_linear p x).
  exact:hJH.
have hzU:U z by rewrite /U hCoordinate;exists x;first exact:hCS x hx.
have hInterior:norm_domain_interior NE U z:=(norm_class_continuous hG hzU).1.
have [u [r [Q [hr [hQ [hQU hQInterior]]]]]]:=critical_local_coordinate_cube_exists hInterior.
have hNullQ:=@critical_chart_cube_image_nullity R m a b Z S C p g A H Y NY hNY f
  u r lambda c Q ha hr hLambda hc hChart hf hA hH hFirst hQ hQU hEta.
have [rho [hRho hBallQ]]:=hQInterior.
pose W:set (real_norm_metric_space hNE):=[set v|mdist (z:real_norm_metric_space hNE) v<rho].
have hW:open W:=metric_open_ball_open (z:real_norm_metric_space hNE) rho.
pose V:set (real_norm_metric_space hNM):=T @^-1` W.
have hV:open V.
  apply:open_comp hW=>q _;exact:hTContinuous.
exists V;split;first exact:hV.
split;first by rewrite /V /W /= /z mdistxx.
apply:(measure_null_subset hMu _ hNullQ).
move=>y [q [hqC hqV] <-].
have hNear:NE (T q-z)<rho.
  change (is_true (NE (z-T q)<rho)) in hqV.
  rewrite /NE (real_seminorm_subtract hNE.1);exact:hqV.
have hTQ:Q (T q).
  have hh:=hBallQ (T q-z) hNear.
  by rewrite addrC subrK in hh.
exists q;last reflexivity.
split;first exact:hqC.
exists (T q);first exact:hTQ.
change (g (H (J (euclidean_projection_linear p q)))=q).
rewrite hJH;exact:(@critical_chart_left_inverse R m (a+b) 1 Z S p g hChart q (hCS q hqC)).
Qed.
