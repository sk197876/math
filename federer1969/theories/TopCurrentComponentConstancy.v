(** Federer (1969), 4.1.26, pp. 383–384:
    apply the original top-current constancy theorem
    to every component outside the closed boundary
    image. The dimension-zero case has no
    negative-degree boundary. No mass or normality
    assumption is imposed on the actual current. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDensityUP CurrentBoundary EuclideanFundamentalCurrent
  CurrentOpenConstantDensity TopCurrentConstancy TopCurrentGlobalConstancy NormOpenComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [top_current_complement_component_constancy]:
    the positive-dimensional constancy step in
    4.1.26, pp. 383–384. The original
    closed exceptional set carries the actual
    boundary support, so every complementary component
    has a constant Euclidean current density. *)
Theorem top_current_complement_component_constancy
    (R:realType) (h2:(1+1:R)!=0) p
    (T:@full_current_space R h2 p.+1 p.+1)
    (B:set (R_n R p.+1)):
  @closed (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) B->
  (@current_support R h2 p.+1 (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R p.+1)) x) p
    (@current_boundary R h2 p.+1 p (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R p.+1)) x) T) `<=` B)->
  forall a,~B a->exists c:R,
    @current_support R h2 p.+1 (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R p.+1)) x) p.+1
      (T-c*:@euclidean_fundamental_current R h2 p.+1) `<=`
      ~`(@connected_component
        (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) (~` B) a).
Proof.
move=>hB hBoundary a ha.
pose X:=R_n R p.+1.
pose N:=inner_norm (@euclidean_inner_productP R p.+1).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R p.+1).
pose XT:=real_norm_metric_space hN.
pose U:=fun _:X=>True.
pose hU:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose C:=@connected_component XT (~` B) a.
have hOpen:open C.
  exact:(@norm_open_components_open R X N hN (~` B) a (closed_openC hB)).
have hConnected:connected C:=@component_connected XT (~` B) a.
have hOutside:@current_support R h2 p.+1 U hU p
    (@current_boundary R h2 p.+1 p U hU T) `<=` (U `&` ~` C).
  move=>x hx;split;first exact:Logic.I.
  move=>hCx;exact:(@connected_component_sub XT (~` B) a x hCx) (hBoundary x hx).
have[c hConstancy]:=@top_current_constancy R h2 p U hU T C
  hOpen hConnected (fun _ _=>Logic.I) hOutside.
rewrite euclidean_fundamental_current_whole_restriction in hConstancy.
exists c;move=>x hx;exact:(hConstancy x hx).2.
Qed.

(** Source for [zero_top_current_complement_component_constancy]:
    dimension zero in the constancy step of
    4.1.26, pp. 383–384. The original
    zero-dimensional theorem supplies the constant
    without a fictitious negative-degree boundary. *)
Theorem zero_top_current_complement_component_constancy
    (R:realType) (h2:(1+1:R)!=0)
    (T:@full_current_space R h2 0%N 0%N)
    (B:set (R_n R 0%N)):
  @closed (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 0%N))) B->
  forall a,~B a->exists c:R,
    @current_support R h2 0%N (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R 0%N)) x) 0%N
      (T-c*:@euclidean_fundamental_current R h2 0%N) `<=`
      ~`(@connected_component
        (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 0%N))) (~` B) a).
Proof.
move=>hB a ha.
pose X:=R_n R 0%N.
pose N:=inner_norm (@euclidean_inner_productP R 0%N).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 0%N).
pose XT:=real_norm_metric_space hN.
pose U:=fun _:X=>True.
pose hU:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
pose C:=@connected_component XT (~` B) a.
have hOpen:open C.
  exact:(@norm_open_components_open R X N hN (~` B) a (closed_openC hB)).
have hConnected:connected C:=@component_connected XT (~` B) a.
have[c hConstancy]:=@zero_dimensional_top_current_constancy R h2 U hU T C
  hOpen hConnected (fun _ _=>Logic.I).
rewrite euclidean_fundamental_current_whole_restriction in hConstancy.
exists c;move=>x hx;exact:(hConstancy x hx).2.
Qed.
