(** Federer (1969), 3.1.20, p. 232: supply the indexed local
    coordinate data, cutoffs and locally finite balls to the sealed
    retraction-patching sequence. Positive ambient dimension is
    treated here; the singleton ambient space is handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormRegularity InnerNormTopologyAdapters MetricClosedBalls
  FedererCoverRadius EuclideanPartitionBallCoverUP OpenEuclideanPartitionCover EuclideanPartitionBumps
  EuclideanPartitionBumpClass EuclideanPartitionLocalFiniteness CountablePartialEnumeration
  PartialEnumerationLocalFiniteness LocallyFiniteFamilyUP RetractionPatchingUP
  SubmanifoldChartsUP SubmanifoldCoordinateCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_retraction_patch_family]: the
    coordinate cover, selected P_i,Q_i and functions u_s of the
    first paragraph of Federer 3.1.20, p. 232. Enumeration is
    univalent on active centers; inactive slots are empty and
    do not affect local finiteness or the eventual domain. *)
Theorem submanifold_retraction_patch_family (R:realType) n mu k
    (B:set (R_n R n.+1)) : @has_convex_coordinate_charts R n.+1 mu k B ->
  exists (U:set (R_n R n.+1)) (P Q:nat->set (R_n R n.+1)),
    is_retraction_patch_family (inner_norm_real_norm (@euclidean_inner_productP R n.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R mu)) B U P Q k /\
    @is_locally_finite_family_on [the topologicalType of real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n.+1))]
      [the choiceType of (nat:Type)] U setT P /\
    forall b,B b -> exists i,Q i b.
Proof.
move=>hB.
pose X:=R_n R n.+1.
pose hBX:=@euclidean_inner_productP R n.+1.
pose NX:=inner_norm hBX.
pose hNX:=inner_norm_real_norm hBX.
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose Phi:set (set (inner_metric_space hBX)):=@convex_coordinate_domain R n.+1 mu k B.
pose U:=\bigcup_(T in Phi) T.
have ho T (hT:Phi T):open T:=convex_coordinate_domain_open hT.
have [S [hS hcov]]:=@open_federer_partition_ball_cover_exists R n Phi ho.
pose radius:=federer_cover_radius Phi.
have [eta he]:=countable_partial_enumeration_exists (partition_ball_centers_countable hS).
pose P:nat->set X:=fun i=>if eta i is Some s then metric_closed_ball s (10*radius s) else set0.
pose Q:nat->set X:=fun i=>if eta i is Some s then [set x|mdist s x<5*radius s] else set0.
have hF:is_retraction_patch_family hNX hNY B U P Q k.
  constructor.
  - move=>i; rewrite /P; case hi:(eta i)=>[s|]; last exact: closed0.
    exact ((@inner_norm_closedP R X (@euclidean_inner_product R n.+1) hBX
      (metric_closed_ball s (10*radius s))).1
      (@metric_closed_ball_closed R (inner_metric_space hBX) s (10*radius s))).
  - move=>i; rewrite /Q; case hi:(eta i)=>[s|]; last exact: open0.
    exact ((@inner_norm_openP R X (@euclidean_inner_product R n.+1) hBX
      [set x|mdist s x<5*radius s]).1
      (@metric_open_ball_open R (inner_metric_space hBX) s (5*radius s))).
  - move=>i; rewrite /Q; case hi:(eta i)=>[s|]; last by move=>x [].
    have hs:=@partial_enumeration_members _ S eta he i s hi.
    move=>x hx; rewrite /U -(partition_fivefold_balls_cover hS).
    exists s=>//; exact: ltW hx.
  - move=>i; case hi:(eta i)=>[s|]; rewrite /P /Q hi.
    2: { left; by split. }
    have hs:=@partial_enumeration_members _ S eta he i s hi.
    have [T [hT hPT]]:=partition_tenfold_balls_subordinate hS hs.
    have [V [phi [psi [hconv [hphi [hpsi [hphiV [him hcan]]]]]]]]:=hT.
    pose u:=euclidean_partition_bump Phi s.
    have huc:=@euclidean_partition_bump_class R n.+1 Phi S ho hS s hs k.
    have hur x:=@euclidean_partition_bump_range R n.+1 Phi S s x hs.
    have hrad:0<radius s.
      apply: (federer_cover_radius_positive ho).
      have [T0 hT0 hx0]:=@partition_ball_centers_in_domain R n.+1 Phi S hS s hs.
      by exists T0.
    have hQP:[set x|mdist s x<5*radius s] `<=` metric_closed_ball s (10*radius s).
      move=>x hx; change (is_true (mdist s x<=10*radius s)); apply: le_trans (ltW hx) _; lra.
    have hu0 x:~metric_closed_ball s (10*radius s) x -> u x=0.
      exact (@euclidean_partition_bump_zero_off_ball R n.+1 Phi S ho hS s x hs).
    have hu1 x:mdist s x<5*radius s -> u x = 1.
      move=>hx; exact (@euclidean_partition_bump_plateau R n.+1 Phi S ho hS s x hs (ltW hx)).
    right; exists T,V,phi,psi,u.
    split; first exact hphi.
    split; first exact hpsi.
    split; first exact hphiV.
    split; first exact him.
    split; first exact hcan.
    split; first exact hconv.
    split; first exact huc.
    split; first exact hur.
    split; first exact hPT.
    split; first exact hQP.
    by split.
exists U,P,Q; split; first exact hF.
split.
- have hLFi:=@partition_tenfold_balls_locally_finite R n.+1 Phi S ho hS.
  have hLFn:=(@inner_norm_locally_finiteP R X (@euclidean_inner_product R n.+1) hBX
    [the choiceType of inner_metric_space hBX] U S
    (fun s=>metric_closed_ball s (10*radius s))).1 hLFi.
  exact (@partial_enumeration_locally_finite (real_norm_metric_space hNX)
    [the choiceType of inner_metric_space hBX] U S
    (fun s=>metric_closed_ball s (10*radius s)) eta he hLFn).
- move=>b hb.
  have hBU:=@convex_coordinate_cover_contains R n.+1 mu k B hB.
  have [s hs hx]:=hcov b (hBU b hb).
  have [i hi]:=@partial_enumeration_cover _ S eta he s hs.
  exists i; by rewrite /Q hi.
Qed.
