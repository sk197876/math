(** Earlier source scope: Federer (1969), 4.1.11, pp. 365–366,
    and the actual simplex generators of 4.1.22, p. 379.
    Normality and convex support of the original join supply
    the earlier polyhedral prerequisites. The retained comments
    also identify their later use in 4.1.32. *)
(** Federer (1969), 4.1.32, pp. 392–393:
    the simplex generators in the printed argument are
    normal. Their join recursion uses only the earlier
    normal segment, Cartesian product and proper smooth
    image laws from 4.1.7–4.1.12. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianNormal CurrentDegreeTransport
  NormalCurrentsUP NormalCurrentDegreeTransport CurrentSegmentMapUP
  OrientedSegmentCurrentSealed OrientedSegmentNormal CurrentJoinDomain
  CurrentJoinSourceChain CurrentJoinSourceCompact CurrentJoinMapSealed
  CurrentJoinMapClass CurrentJoinSealed CurrentJoinLaws CurrentPushforwardNormality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_join_normal]: normal compact
    factors have normal original join, supporting the
    simplex induction used in Federer 4.1.32,
    pp. 392–393. Use the actual ordered product
    S times [0,1] times T, not a new join. *)
Theorem current_join_normal (R:realType) (h2:(1+1:R)!=0) n i j
    (S:@current_space R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) i)
    (T:@current_space R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) j)
    (hS:@is_normal_current R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) i S)
    (hT:@is_normal_current R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) j T):
  @is_normal_current R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) (i+1+j)%N
    (@CurrentJoin.value R h2 n i j S T hS.2 hT.2).
Proof.
pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
pose Full:set X:=fun _=>True.
pose hFull:=fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x.
pose Time:set (R_n R 1%N):=fun _=>True.
pose hTime:=fun (t:R_n R 1%N) (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N)) t.
pose TimeX:=@euclidean_cartesian_set R 1%N n Time Full.
pose hTimeX:=@current_cartesian_domain_open R 1%N n Time Full hTime hFull.
pose Segment:=@current_join_time_segment R h2.
have hSegment:@is_normal_current R h2 1%N Time hTime 1%N Segment.
  exact:(@oriented_segment_current_normal R h2 1%N Time hTime
    (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
    (@current_join_time_segment_domain R)).
pose Inner:=@CartesianCurrentProduct.value R h2 1%N n 1%N j
  Time Full hTime hFull Segment T.
have hInner:=@normal_current_cartesian_product R h2 1%N n Time Full hTime hFull
  1%N j Segment T hSegment hT.
pose Product:=@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
  Full TimeX hFull hTimeX S Inner.
have hProduct:=@normal_current_cartesian_product R h2 n (1+n)%N Full TimeX
  hFull hTimeX i (1+j)%N S Inner hS hInner.
have hChain:=(@normal_current_degree_transport R h2 (n+(1+n))%N
  (@current_join_domain R n) (@current_join_domain_open R n)
  (i+(1+j))%N (i+1+j)%N (addnA i 1%N j) Product).1 hProduct.
rewrite (@current_join_pushforward R h2 n i j S T hS.2 hT.2).
exact:(@current_pushforward_normal R h2 (n+(1+n))%N n
  (@current_join_domain R n) Full (@current_join_domain_open R n) hFull
  (@CurrentJoinMap.value R n) (@current_join_map_image R n)
  (@current_join_map_smooth R n (@current_join_domain R n) (@current_join_domain_open R n))
  (i+1+j)%N (@current_join_source_chain R h2 n i j S T)
  (@current_join_source_proper R h2 n i j S T hS.2 hT.2) hChain).
Qed.
