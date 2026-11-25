(** Federer (1969), 4.1.4, p. 348: the reduction to
    connected open subdomains with compact closure in U.
    This reuses the original compact neighbourhood exhaustion
    and the component and compact-capture theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet SmoothCompactExhaustionUP
  CompactInverseSystemUP ComponentInclusion NormOpenComponents
  DirectedOpenComponentExhaustion DirectedOpenCompactCapture.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactExhaustionConnectedNeighbourhood.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Local Notation T := (real_norm_metric_space hNX).
Variable A:set X.
Hypothesis hConnected:@connected T A.
Variable K:nat->smooth_compact_set hNX A.
Hypothesis hK:is_smooth_compact_exhaustion K.
Variable a:X.
Hypothesis ha:A a.

(** Source for [compact_exhaustion_connected_neighbourhood]:
    each compact subset of connected open A lies with a fixed
    centre in a connected open subdomain with compact closure
    in A, supporting the initial reduction in Federer 4.1.4,
    p. 348. Only the proved compact-exhaustion laws are used. *)
Theorem compact_exhaustion_connected_neighbourhood
    (L:smooth_compact_set hNX A):exists W:set X,
  @open T W /\ @connected T W /\ W a /\
  (smooth_compact_carrier L `<=` W) /\
  @compact T (@closure T W) /\ (@closure T W `<=` A).
Proof.
pose O (j:nat):set T:=@interior T (smooth_compact_carrier (K j)).
have hOpen j:@open T (O j):=open_interior _.
have hInside j:O j `<=` A.
  move=>x hx; exact:(smooth_compact_in_domain (K j) x (interior_subset hx)).
have hMono m n:(m<=n)%N ->O m `<=` O n.
  move=>hmn; apply:interiorS.
  exact:(@smooth_compact_exhaustion_monotone R X NX hNX A K hK m n hmn).
have hCover:forall x,A x ->exists j,O j x.
  move=>x hx.
  pose C:=@smooth_compact_singleton R X NX hNX A x hx.
  have[j [W [hW [hCW hWK]]]]:=@smooth_compact_exhaustion_neighbourhood R X NX hNX A K hK C.
  exists j; apply:(@interiorS T W (smooth_compact_carrier (K j)) hWK x).
  rewrite ((@interior_id T W).1 hW); apply:hCW; reflexivity.
have hDir:forall i j:nat,setT i ->setT j ->exists k:nat,
    setT k /\ (O i `<=` O k) /\ (O j `<=` O k).
  move=>i j _ _; exists (maxn i j); split=>//; split.
  - exact:(hMono i _ (leq_maxl i j)).
  - exact:(hMono j _ (leq_maxr i j)).
pose C (j:nat):set T:=@connected_component T (O j) a.
have hCoverValid:forall x,A x ->exists j,setT j /\ O j x.
  move=>x hx; have[j hj]:=@hCover x hx; exists j; by split.
have hPoint:forall x,A x ->exists j,C j x.
  move=>x hx.
  have[j [_ hj]]:=@directed_open_components_exhaust_connected R X NX hNX
    (Choice.clone nat _) setT A O (fun j _=>hOpen j) (fun j _=>hInside j)
    hCoverValid
    hDir a ha hConnected x hx.
  by exists j.
have hDirected:is_directed_preorder (fun i j:nat=>(i<=j)%N).
  constructor.
  - exists 0%N; by [].
  - exact:leqnn.
  - move=>i j k hij hjk; exact:(leq_trans hij hjk).
  - move=>i j; exists (maxn i j); split; [exact:leq_maxl|exact:leq_maxr].
pose L0:=@smooth_compact_union R X NX hNX A L
  (@smooth_compact_singleton R X NX hNX A a ha).
have hCCover:forall x:T,smooth_compact_carrier L0 x ->exists j,C j x.
  move=>x hx; apply:hPoint; exact:(smooth_compact_in_domain L0 x hx).
have hCOpen j:@open T (C j).
  exact:(@norm_open_components_open R X NX hNX (O j) a (hOpen j)).
have hCMono i j:(i<=j)%N ->C i `<=` C j.
  move=>hij; exact:(@component_inclusion T (O i) (O j) a (hMono i j hij)).
have[j hCapture]:=@directed_open_compact_capture T (Choice.clone nat _)
  (fun i j:nat=>(i<=j)%N) hDirected C (smooth_compact_carrier L0)
  (smooth_compact_is_compact L0) hCOpen hCMono hCCover.
have hCK:C j `<=` smooth_compact_carrier (K j).
  move=>x hx; exact:interior_subset (@connected_component_sub T (O j) a x hx).
have hClosedK:@closed T (smooth_compact_carrier (K j)).
  exact:compact_closed (@metric_hausdorff R T) (smooth_compact_is_compact (K j)).
have hClK:@closure T (C j) `<=` smooth_compact_carrier (K j).
  move=>x hx; have h:=@closureS T _ _ hCK x hx.
  by rewrite -((@closure_id T _).1 hClosedK) in h.
exists (C j); split; first exact:hCOpen.
split; first exact:component_connected.
split; first by apply:hCapture; right.
split; first by move=>x hx; apply:hCapture; left.
split.
- apply:(@subclosed_compact T (@closure T (C j)) (smooth_compact_carrier (K j))).
  + exact:(@closed_closure T (C j)).
  + exact:(smooth_compact_is_compact (K j)).
  + exact:hClK.
- move=>x hx; exact:(smooth_compact_in_domain (K j) x (hClK x hx)).
Qed.
End CompactExhaustionConnectedNeighbourhood.
