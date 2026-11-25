(** Federer (1969), 3.4.2(8), pp. 315–316: apply
    the two-scale cover to an actual adapted projection chart. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP RealPower NormMetric HomeomorphismUP InnerOwnNormTopology OrthogonalMaps
  NormDifferentialUP NormRegularity NormRegularityLinearMaps RelativeClassUP
  NormClassOneCompactLipschitz LipschitzUP EuclideanProjectionSpace
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanBlockCoordinates
  CriticalManifoldFamilyUP CriticalRelativeComposition CriticalOscillation
  PositiveRightOrderLimit MetricRealPowerMeasure CriticalTwoScaleNullity
  CriticalCubeBlocks CriticalAdaptedBlock CriticalBlockDistance CriticalEtaImageBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_cube_image_nullity]: the original
    chart calculation in 3.4.2(8), pp. 315–316. On a compact
    adapted cube, actual class-one maps supply both Lipschitz
    constants. The given eta limit supplies the first-block
    flatness; the cube-cover theorem then proves image nullity.
    The subspace and adapted coordinates are local witnesses
    whose existence is proved separately from the original projection. *)
Theorem critical_chart_cube_image_nullity (R:realType) m a b
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m (a+b)) (g:R_n R (a+b)->R_n R m)
    (A:G (R_n R (a+b)) a) (H:{linear R_n R (a+b)->R_n R (a+b)})
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (f:R_n R m->Y)
    (u:R_n R (a+b)) (r lambda c:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R (a+b)))):
  (0<a)%N ->0<r ->0<lambda ->0<=c ->
  is_critical_manifold_chart 1 Z S p g ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f 1 ->
  (forall y,grassmann_val A y <->exists z,Z z /\euclidean_projection_linear p z=y) ->
  is_orthogonal_map (@euclidean_inner_product R (a+b)) (@euclidean_inner_product R (a+b)) H ->
  (forall z:R_n R (a+b),(forall i:'I_(a+b),(a<=i)%N ->z i=0) ->grassmann_val A (H z)) ->
  is_euclidean_coordinate_cube u r Q ->
  (forall x,Q x ->(euclidean_projection_linear p @` S) (H x)) ->
  positive_right_extended_order_limit (fun delta=>critical_eta NY Z S C f lambda delta) 0%E ->
  @metric_real_power_measure R (real_norm_metric_space hNY) c (b%:R+a%:R/lambda)
    (f @` (C `&` ((fun x=>g (H x)) @` Q)))=0%E.
Proof.
move=>ha hr hLambda hc hChart hf hA hH hFirst hQ hQU hEta.
pose E:=R_n R (a+b).
pose NE:=inner_norm (@euclidean_inner_productP R (a+b)).
pose hNE:=inner_norm_real_norm (@euclidean_inner_productP R (a+b)).
pose NM:=inner_norm (@euclidean_inner_productP R m).
pose hNM:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x:E=>(euclidean_projection_linear p @` S) (H x).
pose G:=fun x:E=>g (H x).
pose F:=fun x:E=>f (G x).
have hNorm x:NE (H x)=NE x:=orthogonal_map_norm
  (@euclidean_inner_productP R (a+b)) (@euclidean_inner_productP R (a+b)) hH x.
have hBounded:norm_bounded_linear NE NE (hom_of_linear H).
  exists 1;split;first exact:ler01.
  by move=>x;change (is_true (NE (H x)<=1*NE x));rewrite hNorm mul1r.
have hG:norm_class hNE hNM U G 1:=@norm_class_precompose_linear R E E (R_n R m)
  NE NE NM hNE hNE hNM (euclidean_projection_linear p @` S) g (hom_of_linear H) 1
  hBounded (critical_chart_inverse_class hChart).
have hMap x:U x ->S (G x).
  move=>hx;exact:(critical_chart_right_inverse hChart hx).1.
have hF:norm_class hNE hNY U F 1:=@critical_relative_class_composition R E (R_n R m) Y
  NE NM NY hNE hNM hNY U S G f 1 hG hMap hf.
have hCompact:@compact (real_norm_metric_space hNE) Q.
  have hImage:=continuous_compact (continuous_subspaceT
    (homeomorphism_continuous (inner_own_norm_homeomorphism (@euclidean_inner_productP R (a+b)))))
    (coordinate_cube_compact hQ).
  by rewrite image_id in hImage.
have [L [hL [hL0 hGBound]]]:=@norm_class_one_compact_lipschitz R E (R_n R m) NE NM hNE hNM U Q G
  ((norm_class_firstP hNE hNM U G).1 hG) hQU hCompact.
have [K [hK [hK0 hFBound]]]:=@norm_class_one_compact_lipschitz R E Y NE NY hNE hNY U Q F
  ((norm_class_firstP hNE hNY U F).1 hF) hQU hCompact.
pose M:=L+K+1.
have hM:0<M by rewrite /M;lra.
have hLM:L<=M by rewrite /M;lra.
have hKM:K<=M by rewrite /M;lra.
have hGControl x y:Q x ->Q y ->NM (G x-G y)<=M*NE (x-y).
  move=>hx hy;have hb:=hGBound x y hx hy.
  exact:le_trans hb (ler_wpM2r (inner_norm_nonnegative _ _) hLM).
have hFControl x y:Q x ->Q y ->NY (F x-F y)<=M*NE (x-y).
  move=>hx hy;have hb:=hFBound x y hx hy.
  exact:le_trans hb (ler_wpM2r (inner_norm_nonnegative _ _) hKM).
have [QA [QB [hQA [hQB hProduct]]]]:=critical_coordinate_cube_blocks hQ.
pose P:set (R_n R a*R_n R b):=
  [set z|Q (euclidean_block_join z) /\C (G (euclidean_block_join z))].
pose FF:=fun x:R_n R a=>fun y:R_n R b=>F (euclidean_block_join (x,y)).
have hJoin z:euclidean_block_join ((euclidean_block_split z).1,
    (euclidean_block_split z).2)=z.
  by rewrite -surjective_pairing euclidean_block_splitK.
have hOriginal:f @` (C `&` (G @` Q))=(fun z=>FF z.1 z.2) @` P.
  apply/seteqP;split.
  - move=>y [x [hxC [z hz hZX]] hXY].
    exists ((euclidean_block_split z).1,(euclidean_block_split z).2).
    + change (Q (euclidean_block_join ((euclidean_block_split z).1,(euclidean_block_split z).2)) /\
        C (G (euclidean_block_join ((euclidean_block_split z).1,(euclidean_block_split z).2)))).
      rewrite hJoin;split;first exact:hz.
      by rewrite hZX.
    + change (F (euclidean_block_join ((euclidean_block_split z).1,(euclidean_block_split z).2))=y).
      rewrite hJoin /F hZX;exact:hXY.
  - move=>y [z [hzQ hzC] hValue].
    exists (G (euclidean_block_join z)).
    + split;first exact:hzC.
      by exists (euclidean_block_join z).
    + have hPair:FF z.1 z.2=F (euclidean_block_join z).
        by rewrite /FF -surjective_pairing.
      rewrite hPair in hValue;exact:hValue.
rewrite hOriginal.
apply:(@critical_two_scale_cube_nullity R a b Y NY hNY FF P
  (euclidean_block_split u).1 (euclidean_block_split u).2 r
  (real_power M lambda) M lambda c QA QB ha hr hLambda
  (real_power_nonnegative _ _) (ltW hM) hc hQA hQB).
- move=>z [hz _];exact:(hProduct _ _).1 hz.
- move=>eps hEps.
  have hEpsE:(0<eps%:E)%E by rewrite lte_fin.
  have [d [hd hSmall]]:=hEta.2 eps%:E hEpsE.
  pose delta:=d/2.
  have hDelta:0<delta by rewrite /delta divr_gt0 // ltr0n.
  have hDeltaD:delta<d by rewrite /delta;lra.
  exists (delta/M);split;first by rewrite divr_gt0.
  move=>q w x [hqw hC] hx hNear.
  have hqwProduct:QA q /\QB w:=(hProduct q w).1 hqw.
  have hxw:Q (euclidean_block_join (x,w)):=(hProduct x w).2 (conj hx hqwProduct.2).
  pose X:=H (euclidean_block_join (x,w)).
  pose V:=H (euclidean_block_join (q,w)).
  have hDistance:NE (X-V)=inner_norm (@euclidean_inner_productP R a) (x-q).
    rewrite /X /V -linearB hNorm;exact:critical_first_block_distance.
  have hFlatZ:=critical_adapted_first_block_difference hFirst x q w.
  have hOriginalZ:exists z,Z z /\euclidean_projection_linear p z=X-V.
    exact:(hA _).1 hFlatZ.
  have hLip:NM (g X-g V)<=M*NE (X-V).
    rewrite hDistance.
    have hh:=hGControl _ _ hxw hqw.
    by rewrite /NE critical_first_block_distance in hh.
  have hNearOriginal:M*NE (X-V)<=delta.
    rewrite hDistance.
    have hh:=hNear;rewrite ler_pdivlMr // in hh.
    by rewrite mulrC.
  have hEtaBound:(critical_eta NY Z S C f lambda delta<=eps%:E)%E:=
    ltW (hSmall delta hDelta hDeltaD).
  have hResult:=@critical_eta_chart_increment_bound R m (a+b) 1 Z S C p g Y NY hNY
    f lambda delta eps M X V hChart (hQU _ hxw) (hQU _ hqw) hC hOriginalZ
    (ltW hEps) (ltW hM) hLambda hLip hNearOriginal hEtaBound.
  change (is_true (NY (f (g X)-f (g V))<=eps*real_power M lambda*
    real_power (NE (X-V)) lambda)) in hResult.
  by rewrite hDistance in hResult.
- move=>x w z hx hw hz.
  have hXW:Q (euclidean_block_join (x,w)):=(hProduct x w).2 (conj hx hw).
  have hXZ:Q (euclidean_block_join (x,z)):=(hProduct x z).2 (conj hx hz).
  have hh:=hFControl _ _ hXW hXZ.
  by rewrite /NE critical_last_block_distance in hh.
Qed.
