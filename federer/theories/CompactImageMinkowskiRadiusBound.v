(** Federer (1969), 3.2.38, pp. 274--275: actual compact
    image tube bounds with one uniform vanishing-error coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanBallVolume NormDifferentialUP
  EuclideanLinearJacobian EuclideanJacobianMeasurable JacobianDensityMeasure LipschitzUP
  BorelFunctionUP RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialContinuityUP
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanUniformRemainderPoints
  CompactDifferentialCoreUP CompactDifferentialCore CompactPartialUniformContinuity
  CompactCoreCubeCoverUP CompactCoreCubeCover JacobianRepresentativeActualGraph CompactCoreJacobianSum
  GoodCubeMinkowskiEstimate LipschitzParentCubeTubeBound FiniteCoreMinkowskiErrorBound ReciprocalCoreErrorBound
  MinkowskiContents MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_image_minkowski_radius_bound]: the complete
    small-radius estimate of Federer 3.2.38, pp. 274--275,
    for positive source dimension. The auxiliary Borel scalar field
    is bounded and agrees with every actual differential; the final
    theorem supplies it locally. Lusin 2.3.5 replaces only the printed
    uniform-mean selection. Actual equal grids, Taylor remainders,
    the full Steiner sum including j=0, and finite good/bad cube
    sums give a coefficient independent of integer and radius.
    No later Minkowski comparison or rectifiable equality is used. *)
Theorem compact_image_minkowski_radius_bound (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R)
    (C:set (inner_metric_space (@euclidean_inner_productP R m))) (L:R):
  (0<m<=n)%N ->compact C ->is_metric_lipschitz_bound setT f L ->
  is_metric_lipschitz setT f ->is_borel_function J ->
  (forall x,0<=J x<=L^+m) ->
  (forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
    J x=euclidean_linear_jacobian m D) ->
  exists K:R,0<=K /\forall v:nat,(0<v)%N ->exists delta:R,0<delta /\
    forall r:R,0<r<delta ->
      (minkowski_tube_quotient m (f @` C) r<=euclidean_jacobian_measure f C+(K/v%:R)%R%:E)%E.
Proof.
move=>/andP[hm0 hmn] hC hBound hLip hBorel hJ hActual.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hm:=euclidean_lebesgue_is_measure R m.
pose t:=fine (mu C).
pose M:=L^+m.
have hMassFinite:mu C \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hm C)); exact:euclidean_compact_finite hC.
have hMass:mu C=t%:E by rewrite /t fineK.
have ht:0<=t by rewrite -lee_fin -hMass; exact:measure_nonnegative hm C.
have hM:0<=M:=exprn_ge0 _ hBound.1.
have [xi [hXi hGood]]:=@good_coordinate_cube_minkowski_estimate R m n hmn f J L hBound hActual.
pose eta:R:=euclidean_unit_ball_volume R n*(1+L* m%:R)^+n/euclidean_unit_ball_volume R (n-m).
have hEta:0<=eta.
  rewrite /eta divr_ge0 //; first apply:mulr_ge0.
  - exact:ltW (euclidean_unit_ball_volumeE R n).2.
  - apply:exprn_ge0; apply:addr_ge0; first exact:ler01.
    apply:mulr_ge0 hBound.1 _; exact:ler0n.
  - exact:ltW (euclidean_unit_ball_volumeE R (n-m)).2.
pose K:=t+M+xi*(t+1)+2*eta.
have hK:0<=K.
  apply:addr_ge0; last by apply:mulr_ge0; [exact:ler0n|exact:hEta].
  apply:addr_ge0; first exact:addr_ge0 ht hM.
  apply:mulr_ge0 hXi _; exact:addr_ge0 ht ler01.
exists K; split=>// v hv.
pose V:R:=v%:R.
pose e:=V^-1.
have hV:0<V by rewrite /V ltr0n.
have hV1:1<=V by rewrite /V ler1n.
have he:0<e by rewrite /e invr_gt0.
have heJet:0<e^+2:=exprn_gt0 _ he.
have [d [E hCore]]:=@compact_differential_core_exists R m n f J C (e^+2) e hLip hBorel hC heJet he.
have [hE [hEC [hHole [hd [hRemainder hContinuous]]]]]:=hCore.
have [dJ [hdJ hUniform]]:=@compact_partial_total_uniform_continuity R X (real_line_metric R)
  E J hE hContinuous e he.
have [dGrid [hdGrid hGrid]]:=@compact_core_cube_cover_exists R m C E e hC hE he hHole.
pose dMin:=Num.min d (Num.min dJ dGrid).
have hdMin:0<dMin by rewrite /dMin !lt_min hd hdJ hdGrid.
have hMV:0<m%:R*V by rewrite mulr_gt0 // ltr0n.
exists (dMin/(m%:R*V)); split; first by rewrite divr_gt0.
move=>r /andP[hr hSmall].
have hMesh:m%:R*(V*r)<dMin.
  move:hSmall; rewrite ltr_pdivlMr //; have hEq:r*(m%:R*V)=m%:R*(V*r) by ring.
  by rewrite hEq.
have hSmallD:m%:R*(V*r)<d.
  apply:lt_le_trans hMesh _; by rewrite /dMin ge_min lexx.
have hSmallJ:m%:R*(V*r)<dJ.
  apply:lt_le_trans hMesh _; rewrite /dMin ge_min.
  apply/orP; right; by rewrite ge_min lexx.
have hSmallGrid:m%:R*(V*r)<dGrid.
  apply:lt_le_trans hMesh _; rewrite /dMin ge_min.
  apply/orP; right; by rewrite ge_min lexx orbT.
have hSide:0<V*r by rewrite mulr_gt0.
have [G [B [aG [aB [QG [QB hCover]]]]]]:=hGrid (V*r) hSide hSmallGrid.
have hPoints i:exists x,(QG i `&` E) x.
  exact:proj1 (set0P (QG i `&` E)) (core_cover_good_meets hCover i).
pose a (i:G):=projT1 (cid (hPoints i)).
have ha i:(QG i `&` E) (a i):=projT2 (cid (hPoints i)).
have hGraph x:E x ->partial_function_graph (extended_euclidean_jacobian f) x (J x)%:E.
  move=>hx; apply:(@jacobian_representative_actual_graph R m n f J x hActual).
  have [D [hD _]]:=hRemainder x hx; by exists D.
have hOsc x y:E x ->E y ->@mdist R X x y<dJ ->`|J x-J y|<=e.
  move=>hx hy hxy; exact:ltW (hUniform x y hx hy hxy).
have hWeighted:=@compact_core_jacobian_cube_sum R m n G f J E aG a QG
  (V*r) e M dJ hLip hE hJ (ltW he) hM hGraph hOsc
  (core_cover_good_cube hCover) ha hSmallJ (core_cover_good_null_overlap hCover).
have hGoodCell i:(minkowski_tube_quotient m (f @` QG i) r<=
    (J (a i)+xi/V)%R%:E*mu (QG i))%E.
  rewrite /mu (coordinate_cube_volume (core_cover_good_cube hCover i)) -EFinM.
  exact:(hGood v r d (aG i) (a i) (QG i) hv hr (core_cover_good_cube hCover i)
    (ha i).1 (hRemainder (a i) (ha i).2) hSmallD).
have hBadCell i:(minkowski_tube_quotient m (f @` QB i) r<=eta%:E*mu (QB i))%E.
  exact:(@lipschitz_parent_cube_normalized_tube_bound R m n hmn f (aB i) r L v
    (QB i) hv hr hBound (core_cover_bad_cube hCover i)).
have hz:0<=xi/V by rewrite divr_ge0 //; exact:ltW hV.
have hTube:=@finite_core_minkowski_error_bound R m n G B f C E aG aB QG QB
  (fun i=>J (a i)) (V*r) r e M (xi/V) eta t hLip hr (ltW he) hM hz hEta
  hEC hMass hCover (fun i=>(andP (hJ (a i))).1) hGoodCell hBadCell hWeighted.
apply:le_trans hTube _; apply:leeD (lexx _) _; rewrite lee_fin.
exact:(@reciprocal_core_error_bound R t M xi eta V hXi hV1).
Qed.
