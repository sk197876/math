(** Federer (1969), 3.2.28, pp. 265–267:
    apply area and coarea on the compact smooth manifolds.
    Supporting prerequisite: every class-one submanifold
    has rectifiable relatively open neighbourhood pieces,
    from its actual 3.1.19(4) coordinate inverses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormDifferentialUP NormRegularity NormClassOneUP
  NormClassOneLocalLipschitz NormOpenPreimage NormCoordinateSystemUP
  EuclideanSubmanifoldUP SubmanifoldChartsUP SubmanifoldStraighteningCoordinates
  InnerNormTopologyAdapters MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws
  MetricBoundedClosureLaws LipschitzUP RectifiableSetUP EuclideanLipschitzRectifiableImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_local_rectifiable]: the local
    rectifiability required for the area/coarea applications
    in Federer 3.2.28, pp. 265–267, by 3.2.14,
    pp. 251–252, and 3.1.19(4), p. 231.
    The chart inverse is Lipschitz on an actual bounded
    parameter ball; dimension zero is included. *)
Theorem submanifold_local_rectifiable (R:realType) n mu k
    (B:set (R_n R n)) a:
  (1<=k)%N ->@is_euclidean_submanifold R n mu k B ->B a ->
  exists U:set (inner_metric_space (@euclidean_inner_productP R n)),
    open U /\U a /\@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n))
      mu (B `&` U).
Proof.
move=>hk hB ha.
pose X:=R_n R n; pose Z:=R_n R mu.
pose hBX:=@euclidean_inner_productP R n.
pose hBZ:=@euclidean_inner_productP R mu.
pose NX:=inner_norm hBX; pose NZ:=inner_norm hBZ.
pose hNX:=inner_norm_real_norm hBX; pose hNZ:=inner_norm_real_norm hBZ.
have [T [V [phi [psi [hTa [hConv [hPhi [hPsi [hPV [hPT [him hcan]]]]]]]]]]]:=
  submanifold_convex_coordinates hB ha.
have hc:is_norm_coordinate_system hNX hNZ B T V phi psi k by constructor.
have hAa:T a:=norm_domain_interior_member hNX hTa.
have hVa:V (phi a):=hPV a hAa.
have hPsi1:norm_class_one NZ NX V psi:=(norm_class_firstP hNZ hNX V psi).1
  (norm_class_lower hk hPsi).
have [C [d [hC [hd [hBallV hLip]]]]]:=
  @norm_class_one_local_lipschitz R Z X NZ NX hNZ hNX V psi (phi a) hVa hPsi1.
pose P:set Z:=[set u|NZ (u-phi a)<d].
pose U:set X:=[set x|T x /\P (phi x)].
have hP:@open [the topologicalType of real_norm_metric_space hNZ] P.
  have hEq:P=[set u:real_norm_metric_space hNZ|mdist (phi a:real_norm_metric_space hNZ) u<d].
    apply:funext=>u; apply:propext.
    change (NZ (u-phi a)<d <->NZ (phi a-u)<d).
    have hN:NZ (phi a-u)=NZ (u-phi a).
      by rewrite /NZ -[phi a-u]opprB inner_normN.
    by rewrite hN.
  rewrite hEq; exact:metric_open_ball_open.
have hU:@open [the topologicalType of inner_metric_space hBX] U.
  apply:(inner_norm_openP hBX U).2.
  exact:(@norm_class_zero_open_preimage R X Z NX NZ hNX hNZ T P phi (norm_class_continuous hPhi) hP).
have hImage:psi @` P=B `&` U.
  apply/seteqP; split=>x.
  - move=>[u hu <-].
    have hv:V u:=hBallV u hu.
    have hi:(psi @` V) (psi u) by exists u.
    rewrite him in hi; split; first exact:hi.1.
    split; first exact:hi.2.
    by rewrite /P hcan.
  - move=>[hBx [hTx hPx]].
    exists (phi x); first exact hPx.
    exact:(@norm_coordinate_base_inverse R X Z NX NZ hNX hNZ B T V phi psi k hc x hBx hTx).
have hBound:@metric_set_bounded R (inner_metric_space hBZ) P.
  apply:(metric_bounded_subset (B:=metric_closed_ball (phi a:inner_metric_space hBZ) d)); last
    exact:covering_closed_ball_bounded (ltW hd).
  move=>u hu; change (inner_norm hBZ (phi a-u)<=d).
  rewrite -[phi a-u]opprB inner_normN; exact:ltW hu.
have hMetricLip:@is_metric_lipschitz R (inner_metric_space hBZ) (inner_metric_space hBX) P psi.
  exists C; split; first exact hC.
  split; first exact:ltW hC.
  move=>u v hu hv; rewrite !inner_metric_distanceE.
  exact:hLip u v hu hv.
exists U; split; first exact hU.
split.
- change (T a /\NZ (phi a-phi a)<d).
  split; first exact hAa.
  by rewrite subrr /NZ inner_norm0.
- rewrite -hImage; exact:euclidean_lipschitz_bounded_image_rectifiable hBound hMetricLip.
Qed.
