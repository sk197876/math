(** Federer (1969), 4.1.18, p. 374: a compact
    parameter current allows local comparison of its
    actual slices. This is the support argument behind
    the original averaged transgression; it reuses
    4.1.8 and the compact tube principle.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockNormTopology EuclideanCartesianMap TopologicalProductMaps
  CompactProductTube ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing
  CurrentSpaces CurrentCartesianDomain CurrentCartesianVectorProduct CurrentCartesianSliceSealed
  CurrentCartesianSliceTestSealed CurrentCartesianSliceTestPairing
  CurrentTestNearSupportAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceNearSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Local Notation Z:=(R_n R (m+n)%N).
Local Notation hN k:=(inner_norm_real_norm (@euclidean_inner_productP R k)).
Local Notation XT:=(real_norm_metric_space (hN m)).
Local Notation YT:=(real_norm_metric_space (hN n)).
Local Notation ZT:=(real_norm_metric_space (hN (m+n)%N)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall x,A x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB:forall y,B y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B y.
Local Notation AB:=(@euclidean_cartesian_set R m n A B).
Local Notation hAB:=(@current_cartesian_domain_open R m n A B hA hB).
Local Notation DC:=(@current_test_space R h2 (m+n)%N AB hAB (i+j)%N).
Local Notation vc:=(@current_test_value R h2 (m+n)%N AB hAB (i+j)%N).
Local Notation va:=(@current_test_value R h2 m A hA i).
Local Notation vb:=(@current_test_value R h2 n B hB j).
Variable S:@current_space R h2 m A hA i.
Hypothesis hCompact:@compact XT (@current_support R h2 m A hA i S).
Local Notation Slice:=(@CartesianSlice.value R h2 m n i j A B hA hB S).

(** Source for [current_cartesian_slice_near_support]:
    agreement near spt S times {x} persists on
    an open neighbourhood of x and fixes the
    actual slices, supporting 4.1.18, p. 374.
    Empty parameter support is retained. *)
Theorem current_cartesian_slice_near_support
    (phi psi:DC) x (hx:B x) (O:set Z):
  @open ZT O ->
  (forall a,@current_support R h2 m A hA i S a->
    O (euclidean_block_join (a,x))) ->
  (forall y,O y->vc phi y=vc psi y) ->
  exists W:set Y,@open YT W /\W x /\W `<=` B /\
    forall y,W y->vb (Slice phi) y=vb (Slice psi) y.
Proof.
move=>hO hSO hMatch.
have hPair:continuous (fun z:(YT*XT)%type=>(z.2,z.1):(XT*YT)%type).
  apply:topological_pair_continuous.
  - exact:second_projection_continuous.
  - exact:first_projection_continuous.
pose J (z:Y*X):Z:=euclidean_block_join (z.2,z.1).
have hJ:continuous (fun z:(YT*XT)%type=>(J z:ZT)).
  move=>z;exact:(continuous_comp (@hPair z)
    (@euclidean_block_join_norm_continuous R m n (z.2,z.1))).
have hPre:@open [the topologicalType of (YT*XT)%type] (J @^-1` O).
  apply:open_comp hO=>z _;exact:hJ z.
have [W [D [hW [hxW [hD [hSD hWD]]]]]]:=
  @compact_product_open_tube YT XT x
    (@current_support R h2 m A hA i S) (J @^-1` O)
    hCompact hPre (fun a ha=>hSO a ha).
have hBOpen:@open YT B.
  rewrite openE=>y hy.
  exact:(@norm_domain_interior_neighbourhood R Y
    (inner_norm (@euclidean_inner_productP R n)) (hN n) B y).1 (@hB y hy).
have hAOpen:@open XT A.
  rewrite openE=>a ha.
  exact:(@norm_domain_interior_neighbourhood R X
    (inner_norm (@euclidean_inner_productP R m)) (hN m) A a).1 (@hA a ha).
exists (W `&` B);split;first exact:openI hW hBOpen.
split;first exact:conj hxW hx.
split;first by move=>y hy;exact:hy.2.
move=>y [hyW hyB];apply:pairing_ext=>eta.
rewrite !(@CartesianSlice.laws R h2 m n i j A B hA hB S _ y hyB eta).
apply:(@current_test_near_support_values_equal R h2 m i A hA S
  (@CartesianSliceTest.value R h2 m n A B hA hB i j y hyB eta phi)
  (@CartesianSliceTest.value R h2 m n A B hA hB i j y hyB eta psi)
  (D `&` A) (openI hD hAOpen)).
- move=>a ha;exact:conj (hSD a ha) ha.1.
- move=>a [haD haA];apply:pairing_ext=>xi.
  rewrite !(@current_cartesian_slice_test_pairing R h2 m n i j A B hA hB
    y hyB eta _ a haA xi).
  exact:(congr1 (pairing (@current_cartesian_vector_product R m n i j xi eta))
    (hMatch (J (y,a)) (hWD (y,a) (conj hyW haD)))).
Qed.
End CurrentCartesianSliceNearSupport.
