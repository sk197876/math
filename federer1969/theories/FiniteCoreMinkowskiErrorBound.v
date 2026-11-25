(** Federer (1969), 3.2.38, p. 275: sum actual
    tube estimates and the compact-core Jacobian comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanCoordinateCubeGeometry
  EuclideanCoordinateCubeUP CompactCoreCubeCoverUP EqualCoordinateCubeGridMeasure
  FiniteTwoMinkowskiTubeCover MinkowskiContents JacobianDensityMeasure LipschitzUP
  MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_core_minkowski_error_bound]: the final
    finite-family estimate in Federer 3.2.38, p. 275.
    The compact-core proof retains the Jacobian sum and all
    outside-core mass errors explicitly before taking limits.
    The two real constants are uniform over the finite families.
    Actual coordinate faces justify both volume sums. *)
Lemma finite_core_minkowski_error_bound (R:realType) m n (G B:finType)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (C E:set (inner_metric_space (@euclidean_inner_productP R m)))
    (aG:G->R_n R m) (aB:B->R_n R m) QG QB (c:G->R) (h r e M z eta t:R):
  is_metric_lipschitz setT f ->0<r ->0<=e ->0<=M ->0<=z ->0<=eta ->
  E `<=` C ->@euclidean_lebesgue_measure R m C=t%:E ->
  is_compact_core_cube_cover C E h e aG aB QG QB ->
  (forall i,0<=c i) ->
  (forall i,(minkowski_tube_quotient m (f @` QG i) r<=
    (c i+z)%R%:E*@euclidean_lebesgue_measure R m (QG i))%E) ->
  (forall i,(minkowski_tube_quotient m (f @` QB i) r<=
    eta%:E*@euclidean_lebesgue_measure R m (QB i))%E) ->
  (\sum_i (c i)%:E*@euclidean_lebesgue_measure R m (QG i)<=
    euclidean_jacobian_measure f E+e%:E*@euclidean_lebesgue_measure R m E+
      M%:E*@euclidean_lebesgue_measure R m ((\bigcup_i QG i) `\` E))%E ->
  (minkowski_tube_quotient m (f @` C) r<=euclidean_jacobian_measure f C+
    (e*t+M*e+z*(t+e)+eta*(2*e))%R%:E)%E.
Proof.
move=>hLip hr he hM hz hEta hEC hMass hCover hc hGood hBad hWeighted.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hm:=euclidean_lebesgue_is_measure R m.
pose hn:=euclidean_jacobian_measure_is_measure hLip.
pose UG:=\bigcup_i QG i.
pose UB:=\bigcup_i QB i.
have hMeas (a:R_n R m) Q:is_euclidean_coordinate_cube a h Q ->measure_measurable mu Q.
  move=>hQ; apply:euclidean_borel_measurable.
  exact:closed_borel_set (compact_closed (@metric_hausdorff R X) (coordinate_cube_compact hQ)).
have hGoodSum:mu UG=(\sum_i mu (QG i))%E.
  exact:(@finite_coordinate_cubes_measure_sum R m G aG h QG mu hm
    (core_cover_good_cube hCover) (fun i=>hMeas _ _ (core_cover_good_cube hCover i))
    (core_cover_good_null_overlap hCover)).
have hBadSum:mu UB=(\sum_i mu (QB i))%E.
  exact:(@finite_coordinate_cubes_measure_sum R m B aB h QB mu hm
    (core_cover_bad_cube hCover) (fun i=>hMeas _ _ (core_cover_bad_cube hCover i))
    (core_cover_bad_null_overlap hCover)).
have hCoverBound:=@finite_two_minkowski_image_tube_cover R X n m G B f C QG QB r hr
  (core_cover_source hCover).
have hGoodBound:(\sum_i minkowski_tube_quotient m (f @` QG i) r<=
    (\sum_i (c i)%:E*mu (QG i))+z%:E*mu UG)%E.
  have hSum:(\sum_i minkowski_tube_quotient m (f @` QG i) r<=
    \sum_i ((c i+z)%R%:E*mu (QG i)))%E by apply:lee_sum=>i _; exact:hGood i.
  apply:le_trans hSum _.
  have hCell i:((c i+z)%R%:E*mu (QG i)=
    (c i)%:E*mu (QG i)+z%:E*mu (QG i))%E.
    rewrite EFinD; apply:ge0_muleDl; by rewrite lee_fin.
  rewrite (eq_bigr _ (fun i _=>hCell i)) big_split hGoodSum ge0_sume_distrr;
    first exact:lexx.
  move=>i _; exact:measure_nonnegative hm _.
have hBadBound:(\sum_i minkowski_tube_quotient m (f @` QB i) r<=eta%:E*mu UB)%E.
  rewrite hBadSum ge0_sume_distrr; last by move=>i _; exact:measure_nonnegative hm _.
  apply:lee_sum=>i _; exact:hBad i.
have hMain:=le_trans hCoverBound (leeD hGoodBound hBadBound).
have hStep:(minkowski_tube_quotient m (f @` C) r<=
    (nu E+e%:E*mu E+M%:E*mu (UG `\` E))+z%:E*mu UG+eta%:E*mu UB)%E.
  apply:le_trans hMain _; exact:leeD (leeD hWeighted (lexx _)) (lexx _).
have hE:(e%:E*mu E<=(e*t)%R%:E)%E.
  rewrite EFinM -hMass; apply:lee_wpmul2l; first by rewrite lee_fin.
  exact:(@measure_mono R X mu hm E C hEC).
have hOutside:(M%:E*mu (UG `\` E)<=(M*e)%R%:E)%E.
  rewrite EFinM; apply:lee_wpmul2l; first by rewrite lee_fin.
  exact:core_cover_good_outside hCover.
have hG:(z%:E*mu UG<=(z*(t+e))%R%:E)%E.
  rewrite EFinM EFinD -hMass; apply:lee_wpmul2l; first by rewrite lee_fin.
  exact:core_cover_good_mass hCover.
have hB:(eta%:E*mu UB<=(eta*(2*e))%R%:E)%E.
  rewrite EFinM; apply:lee_wpmul2l; first by rewrite lee_fin.
  exact:core_cover_bad_mass hCover.
apply:le_trans hStep _.
have hFinal:=leeD (leeD (leeD (leeD (@measure_mono R X nu hn E C hEC) hE) hOutside) hG) hB.
rewrite -!addeA -!EFinD !addrA in hFinal.
exact hFinal.
Qed.
