(** Federer (1969), 3.2.33, p. 270: under the
    global analytic rank bound, the actual rank-mu
    stratum is relatively open in W. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerNormTopologyAdapters RealNormUP NormMetric NormClassOneUP
  NormClassOneActualField NormRegularity NormOpenPreimage NormCoordinateSystemUP
  NormAnalyticUP NormAnalyticLocal NormAnalyticRelativeUP NormAnalyticRelativeComposition
  AnalyticSubmanifoldUP AnalyticSubmanifoldCoordinateSystems EuclideanAnalyticDifferentialField
  RelativeLowImageLocus RelativeRankLocus AnalyticCoordinateRankLocus
  LinearRankUP LinearRankAtLeast RankThresholdOpen EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.

(** Source for [analytic_relative_maximal_rank_open]: the
    openness part of the analytic stratum alternative in
    Federer 3.2.33, p. 270. In actual analytic
    coordinates, derivative continuity makes rank at least
    mu open; the proved global upper bound makes it
    exactly mu. Inverse chart laws return the original
    intrinsic relative rank. All natural degrees are retained. *)
Theorem analytic_relative_maximal_rank_open (R:realType) n m v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n m W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  relative_low_image_locus mu W F = W ->
  @relatively_open_set (inner_metric_space (@euclidean_inner_productP R n)) W
    (relative_rank_locus mu W F).
Proof.
move=>hW hF hAll.
pose X:=R_n R n; pose Z:=R_n R m; pose Y:=R_n R v.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R v).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R v).
pose M:=inner_metric_space (@euclidean_inner_productP R n).
pose S:=relative_rank_locus mu W F.
have hSW:S `<=` W by move=>x hx; exact hx.1.1.
have hNeighbour a (ha:S a):exists O:set M,open O /\O a /\W `&` O `<=` S.
  have haW:=hSW a ha.
  have [T [V [phi [psi [haT [hConvex [hPhi [hPsi hc]]]]]]]]:=
    analytic_submanifold_coordinate_system_exists hW haW.
  have hCoordinate:=@relative_analytic_in_parametrisation R X Z Y NX NZ NY hNX hNZ hNY
    setT W V psi F (fun u hu=>(norm_coordinate_backward_membership hc hu).1) hPsi hF.
  have [D [hD hDAnalytic]]:=euclidean_analytic_differential_field_exists hCoordinate.
  have hField:is_norm_class_one_field NZ NY V (fun u=>F (psi u)) D.
    apply:(@norm_class_one_actual_field R Z Y NZ NY hNZ hNY V (fun u=>F (psi u)) D _ hD).
    exact:(norm_class_firstP hNZ hNY V (fun u=>F (psi u))).1
      (norm_analytic_class_all_orders hCoordinate 1%N).
  have hCriterion q x (hx:W x) (ht:T x):relative_low_image_locus q W F x <->
      exists r,has_linear_rank (D (phi x)) r /\(r<=q)%N.
    exact:(@analytic_coordinate_low_image_iff R n m v q W T V phi psi F D
      hc hPhi hPsi hF hD x hx ht).
  have hExact x (hx:W x) (ht:T x):S x <->has_linear_rank (D (phi x)) mu.
    exact:(relative_rank_locus_coordinate_iff mu (fun q=>hCriterion q x hx ht)).
  pose U:set Z:=[set u|V u /\linear_rank_at_least (D u) mu].
  have hUopen:@open (real_norm_metric_space hNZ) U.
    exact:(@rank_threshold_open R Z Y NZ (@euclidean_inner_product R m)
      (@euclidean_inner_product R v) hNZ (@euclidean_inner_productP R m) (@euclidean_inner_productP R v)
      m (@coordinate_basis R m) (@coordinate_basisP R m) erefl V D
      (fun x hx=>(norm_class_one_zero hField hx).1) (norm_class_one_continuity hField) mu).
  pose O:set M:=[set x|T x /\U (phi x)].
  have hOopen:open O.
    apply:(inner_norm_openP (@euclidean_inner_productP R n) O).2.
    exact:(@norm_class_zero_open_preimage R X Z NX NZ hNX hNZ T U phi
      (norm_class_continuous (norm_coordinate_class_forward hc)) hUopen).
  have haRank:has_linear_rank (D (phi a)) mu:=(hExact a haW haT).1 ha.
  exists O; split; first exact hOopen.
  split.
  - split; first exact haT; split; first exact:(@norm_coordinate_forward_range R X Z NX NZ hNX hNZ W T V phi psi 1%N hc a haT).
    exact:(linear_rank_at_leastP mu haRank).2 (leqnn mu).
  - move=>x [hx [ht [hv hAtLeast]]]; apply:(hExact x hx ht).2.
    have hxLow:relative_low_image_locus mu W F x by rewrite hAll.
    have [r [hRank hr]]:=(hCriterion mu x hx ht).1 hxLow.
    have hMu:=(linear_rank_at_leastP mu hRank).1 hAtLeast.
    have he:r=mu by apply/eqP; rewrite eqn_leq hr hMu.
    by rewrite -he.
pose C:set (set M):=[set O:set M|open O /\W `&` O `<=` S].
exists (\bigcup_(O in C) O); split; first by apply:bigcup_open=>O hO; exact hO.1.
apply/seteqP; split=>x hx.
- split; first exact:hSW x hx.
  have [O [hO [hxo hSub]]]:=hNeighbour x hx.
  exists O; last exact hxo; by split.
- have [hxW [O hO hxO]]:=hx; exact:hO.2 x (conj hxW hxO).
Qed.
