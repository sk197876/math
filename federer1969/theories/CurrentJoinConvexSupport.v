(** Earlier source scope: Federer (1969), 4.1.11, pp. 365–366,
    and the actual simplex generators of 4.1.22, p. 379.
    Normality and convex support of the original join supply
    the earlier polyhedral prerequisites. The retained comments
    also identify their later use in 4.1.32. *)
(** Federer (1969), 4.1.32, p. 392: the
    original simplex support lies in its vertex hull.
    A join of two currents supported in a convex
    set has support there by the old exact Cartesian
    support bound and F(x,t,y)=(1-t)x+ty.
    No representation premise is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentSpaces CurrentSupportGeometry CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianSupportUpper CurrentDegreeTransport
  CurrentDegreeTransportSupport CurrentSegmentMapUP CurrentSegmentCompactSet
  ConvexMetricSegment OrientedSegmentCurrentSealed OrientedSegmentCurrentSupport
  CurrentJoinDomain CurrentJoinSourceChain CurrentJoinMapUP CurrentJoinMapSealed
  CurrentJoinSealed CurrentJoinLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_join_convex_support]: the
    join support is contained in any convex set
    carrying both factors. This is the original
    geometric support fact used for the simplex
    induction in 4.1.32, p. 392. *)
Theorem current_join_convex_support (R:realType) (h2:(1+1:R)!=0) n i j
    (S:@current_space R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) i)
    (T:@current_space R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) j)
    (hS:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _=>True)
        (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) i S))
    (hT:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _=>True)
        (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) j T))
    (H:set (R_n R n)) (hH:is_inner_convex H)
    (hSH:@current_support R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) i S `<=` H)
    (hTH:@current_support R h2 n (fun _=>True)
      (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) j T `<=` H):
  @current_support R h2 n (fun _=>True)
    (fun (x:R_n R n) (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) (i+1+j)%N
    (@CurrentJoin.value R h2 n i j S T hS hT) `<=` H.
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
pose Inner:=@CartesianCurrentProduct.value R h2 1%N n 1%N j
  Time Full hTime hFull Segment T.
move=>y hy.
have[z hz <-]:=@current_join_support_image R h2 n i j S T hS hT y hy.
rewrite /current_join_source_chain current_degree_transport_support in hz.
have[hFirst hInner]:=@current_cartesian_support_upper R h2 n (1+n)%N i (1+j)%N
  Full TimeX hFull hTimeX S Inner z hz.
pose p:=@euclidean_first_block_map R n (1+n)%N z.
pose q:=@euclidean_last_block_map R n (1+n)%N z.
have[hTimeSupport hLast]:=@current_cartesian_support_upper R h2 1%N n 1%N j
  Time Full hTime hFull Segment T q hInner.
pose a:=@euclidean_first_block_map R 1%N n q.
pose b:=@euclidean_last_block_map R 1%N n q.
have hTimeCompact:=@oriented_segment_current_support R h2 1%N Time hTime
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
  (@current_join_time_segment_domain R) a hTimeSupport.
have[t [ht hTimeValue]]:=@current_segment_compact_points R 1%N Time
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
  (@current_join_time_segment_domain R) a hTimeCompact.
have ha:a=@euclidean_one_embed R t.
  rewrite hTimeValue;apply/ffunP=>k.
  rewrite /metric_segment_point /euclidean_one_embed !ffunE.
  change (0+t*(1-0)=t).
  by rewrite subr0 mulr1 add0r.
have hzValue:z=@euclidean_block_join R n (1+n)%N
    (p,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,b)).
  rewrite -ha.
  rewrite /p /q /a /b /euclidean_first_block_map /euclidean_last_block_map.
  by rewrite !euclidean_block_splitK.
rewrite hzValue CurrentJoinMap.laws.
move:ht;rewrite in_itv /=;move/andP=>[ht0 ht1].
exact:hH p b (hSH p hFirst) (hTH b hLast) t ht0 ht1.
Qed.
