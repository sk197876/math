(** Federer (1969), 4.1.26, p. 384: the
    boundary of the actual image current is
    supported in f(Bdry A). Boundedness of
    A makes this exceptional image compact.
    The original boundary and support laws suffice;
    no finite-perimeter hypothesis is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  MetricDiameter MetricBoundedClosureLaws EuclideanDistributionMeasureContext
  CurrentSpaces CurrentBoundary FlatCurrentsUP CurrentLocallyFlatBoundary
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzPushforwardBoundary LipschitzUP LipschitzBasic MetricLocalLipschitzContinuity
  EuclideanCharacteristicCurrent EuclideanLebesgueDimensions MeasureUP
  CurrentBoundedCharacteristicFlat CurrentCharacteristicBoundarySupport
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_source_boundary]:
    Bdry A in the proof of 4.1.26,
    p. 384, is the intersection of
    the closures of A and its complement.
    This is an abbreviation of the original
    topological closure operations. *)
Definition lipschitz_degree_source_boundary (R:realType) m
    (A:set (R_n R m)):set (R_n R m):=
  (@closure (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) A `&`
   @closure (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) (~` A)).

(** Source for [lipschitz_degree_source_boundary_compact]:
    bounded A has compact Bdry A,
    supporting the complementary-component argument
    in 4.1.26, pp. 383–384. No
    source openness, nonemptiness or smoothness is assumed. *)
Theorem lipschitz_degree_source_boundary_compact (R:realType) m
    (A:set (R_n R m)):
  @metric_set_bounded R (inner_metric_space (@euclidean_inner_productP R m)) A->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (lipschitz_degree_source_boundary A).
Proof.
move=>hBound.
pose IT:=inner_metric_space (@euclidean_inner_productP R m).
pose NT:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)).
pose C:=@closure IT A.
have hC:@compact NT C.
  have hImage:=@continuous_compact IT NT (fun x=>x) C
    (continuous_subspaceT (@euclidean_distribution_inner_to_norm R m))
    (@euclidean_bounded_closure_compact R m A hBound).
  by rewrite image_id in hImage.
have hCClosed:@closed NT C:=compact_closed (@metric_hausdorff R NT) hC.
have hInside:@closure NT A `<=` C.
  move=>x hx;apply:hCClosed.
  exact:(@closureS NT A C (fun y hy=>@subset_closure IT A y hy) x hx).
apply:(@subclosed_compact NT (lipschitz_degree_source_boundary A) C).
- exact:(@closedI NT _ _ (@closed_closure NT A) (@closed_closure NT (~` A))).
- exact:hC.
- move=>x hx;exact:hInside x hx.1.
Qed.

(** Source for [lipschitz_degree_boundary_image_compact]:
    f(Bdry A) is compact and hence
    closed in the original target Euclidean
    topology, supporting 4.1.26, pp. 383–384.
    Empty A and dimension zero are included. *)
Theorem lipschitz_degree_boundary_image_compact (R:realType) m
    (f:R_n R m->R_n R m)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R m)) setT f)
    (A:set (R_n R m))
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (f @` lipschitz_degree_source_boundary A).
Proof.
pose NT:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)).
have hLocal:@is_locally_metric_lipschitz R NT NT setT f:=metric_lipschitz_is_local hLip.
have hContinuous:continuous (f:NT->NT):=metric_local_lipschitz_continuous_whole hLocal.
exact:(continuous_compact (continuous_subspaceT hContinuous)
  (lipschitz_degree_source_boundary_compact hBound)).
Qed.

(** Source for [lipschitz_degree_image_boundary_support]:
    spt boundary[f_#(E^m restricted to A)]
    is contained in f(Bdry A), the
    last displayed support inclusion in the
    proof of 4.1.26, p. 384. This
    is the positive-dimensional boundary clause. *)
Theorem lipschitz_degree_image_boundary_support (R:realType)
    (h2:(1+1:R)!=0) p (f:R_n R p.+1->R_n R p.+1)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R p.+1))
      (inner_metric_space (@euclidean_inner_productP R p.+1)) setT f)
    (A:set (R_n R p.+1))
    (hA:measure_measurable (@euclidean_lebesgue_measure R p.+1) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R p.+1)) A):
  let Full:=fun _:R_n R p.+1=>True in
  let hFull:=fun x (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R p.+1)) x in
  let T:=@euclidean_characteristic_current R h2 p.+1 A hA in
  let hT:=@current_bounded_characteristic_flat R h2 p.+1 A hA hBound in
  let hLocal:=@metric_lipschitz_is_local R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p.+1))) setT f hLip in
  @current_support R h2 p.+1 Full hFull p
    (@current_boundary R h2 p.+1 p Full hFull
      (@CurrentFlatLipschitzPushforward.value R h2 p.+1 p.+1 p.+1 Full Full
        hFull hFull f (fun _ _=>Logic.I) hLocal T hT)) `<=`
    f @` lipschitz_degree_source_boundary A.
Proof.
move=>Full hFull T hT hLocal.
pose hBoundary:=@flat_current_boundary R h2 p.+1 p Full hFull T hT.
rewrite (@current_flat_lipschitz_pushforward_boundary R h2 p.+1 p.+1 p
  Full Full hFull hFull f (fun _ _=>Logic.I) hLocal T hT hBoundary).
move=>y hy.
have[x hx hxy]:=@current_flat_lipschitz_pushforward_support R h2 p.+1 p.+1 p
  Full Full hFull hFull f (fun _ _=>Logic.I) hLocal
  (@current_boundary R h2 p.+1 p Full hFull T) hBoundary y hy.
exists x;last exact:hxy.
exact:(@euclidean_characteristic_boundary_support R h2 p A hA x hx).
Qed.
