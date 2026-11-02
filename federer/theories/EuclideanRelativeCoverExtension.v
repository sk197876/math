(** Federer (1969), 3.1.22, p. 236: a single ambient
    class-k extension on an open union, using 3.1.13. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness InnerNormTopologyAdapters NormMetric NormDifferentialUP NormBoundedLinearTopology NormRegularity
  NormClassZeroTopology CompactSupportFunctionUP ContinuousMultilinearUP ContinuousMultilinearSealed
  RelativeClassUP RelativePartitionExtension EuclideanPartitionBallCoverUP EuclideanPartitionBallCover
  EuclideanPartitionFamilyUP EuclideanPartitionFamilySealed NormPartitionUnityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_relative_cover_extension]: the partition
    argument in Federer 3.1.22, p. 236, using the proved
    partition family of 3.1.13, pp. 224–225. The open
    cover is arbitrary and need not be countable. Class zero
    is also allowed; no completeness assumption is added to Y. *)
Theorem euclidean_relative_cover_extension (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (A S:set (R_n R n)) (f:R_n R n->Y) k
    (Phi:set (set (inner_metric_space (@euclidean_inner_productP R n)))) :
  (forall T,Phi T -> exists g,
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY T g k /\
    forall x,S x -> T x -> A x /\ f x=g x) ->
  S `<=` (\bigcup_(T in Phi) T) ->
  exists G,@is_norm_relative_extension R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n)) NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A S f k
    (\bigcup_(T in Phi) T) G.
Proof.
move=>hPhi hSU.
pose X:=R_n R n.
pose M:=inner_metric_space (@euclidean_inner_productP R n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hAbs:=scalar_absolute_value_norm R.
pose U:set M:=\bigcup_(T in Phi) T.
have ho T (hT:Phi T):@open M T.
  have [g [hg _]]:=hPhi T hT.
  exact ((@inner_norm_openP R X _ (@euclidean_inner_productP R n) T).2
    (@norm_class_zero_domain_open R X Y NX NY hNX T g (norm_class_continuous hg))).
have hU:@open M U by apply: bigcup_open=>T hT; exact: ho T hT.
have hUn:@open (real_norm_metric_space hNX) U:=(@inner_norm_openP R X _ (@euclidean_inner_productP R n) U).1 hU.
have hUint x (hx:U x):norm_domain_interior NX U x.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U x).2
    (open_nbhs_nbhs (conj hUn hx))).
have hSA:S `<=` A.
  move=>x hx; have [T hT hxT]:=hSU x hx.
  have [g [hg hag]]:=hPhi T hT; exact (hag x hx hxT).1.
have [C hC]:=@federer_partition_ball_cover_exists R n Phi ho.
pose Z:=fun j=>@ContinuousMultilinear.space R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs.
pose ev:=fun j=>@ContinuousMultilinear.evaluation R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X R^o NX (fun t:R^o=>`|t|) hNX hAbs.
pose rho:=@EuclideanPartitionFamily.functions R n Z ev ZN hZ Phi C ho hC.
have hFamily:=@EuclideanPartitionFamily.laws R n Z ev ZN hZ Phi C ho hC.
have hex (s:M):exists tg:(set M)*(X->Y),C s ->
    norm_class hNX hNY tg.1 tg.2 k /\
    real_function_support (rho s) `<=` tg.1 /\
    forall x,S x -> tg.1 x -> f x=tg.2 x.
  case:(pselect (C s))=>[hs|hs]; last by exists (set0,(fun _=>0)).
  have [T [hT hb]]:=partition_tenfold_balls_subordinate hC hs.
  have [g [hg hag]]:=hPhi T hT.
  exists (T,g); move=>_; split; first exact hg.
  split.
  - exact (subset_trans (partition_family_support_ball hFamily hs) hb).
  - move=>x hx hxT; exact (hag x hx hxT).2.
have [tg htg]:=choice hex.
apply: (@relative_partition_extension R X Y M NX NY hNX hNY A S U f k C rho
  (fun s=>(tg s).1) (fun s=>real_function_support (rho s)) (fun s=>(tg s).2)
  hUint hSU hSA (norm_partition_locally_finite (partition_family_partition hFamily))
  (norm_partition_sum_one (partition_family_partition hFamily))).
- move=>s hs; exact (partition_family_global_smooth hFamily hs k).
- move=>s hs; exact (htg s hs).1.
- move=>s hs; exact ((@inner_norm_closedP R X _ (@euclidean_inner_productP R n) _).1 (@real_function_support_closed R M (rho s))).
- move=>s hs; exact (htg s hs).2.1.
- move=>s hs x hx; exact (real_function_zero_off_support hx).
- move=>s hs; exact (htg s hs).2.2.
Qed.
