(** Federer (1969), 4.1.18, p. 374: the
    old smooth deformation acts on compact tests by
    the original homotopy transgression. This is the
    arbitrary-current duality needed before averaging;
    neither compact current support nor finite mass
    is assumed.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentSpaces CurrentSupportGeometry
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductAction
  CurrentCartesianSupportEquality CurrentCartesianSliceSealed CurrentCartesianSliceNearSupport
  CurrentTestLocalSupportAgreement CurrentTestNearSupportAgreement
  CurrentPushforwardUP CurrentPushforwardExistence CurrentPushforwardSealed
  SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackSealed
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentHomotopyTimeSegment CurrentHomotopyProductSupport CurrentSegmentCompactSet
  OrientedSegmentCurrentSupport CurrentHomotopyTransgressionSealed
  CurrentHomotopyTransgressionLocalTest CurrentHomotopyTestReplacementUP
  CurrentDeformationChainSealed CurrentDeformationChainPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDeformationChainTestAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hH.1.
Local Notation hU:=(@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV:=(@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval:=(@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hInterval).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation S:=(@current_homotopy_time_segment R A hInterval h2).
Local Notation hSegment:=(@current_homotopy_time_segment_domain R A hInterval).
Local Notation KTime:=(@current_segment_compact_set R 1%N AT
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) hSegment).
Local Notation DU:=(@current_test_space R h2 n U hU j).
Local Notation DV:=(@current_test_space R h2 nu V hV (1+j)%N).
Local Notation value:=(@current_test_value R h2 n U hU j).
Local Notation image:=(@current_homotopy_image R n nu A U V f g h geometry).
Local Notation F:=(@current_smooth_space R h2 nu V hV (1+j)%N).
Local Notation Inc:=(smooth_test_inclusion (@current_smooth_space_laws R h2 nu V hV (1+j)%N)).
Variable T:@current_space R h2 n U hU j.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Local Notation P:=(@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU S T).
Local Notation properP:=(@current_homotopy_product_proper R h2 n nu j A U V f g h geometry T hProper).
Local Notation chain:=(@CurrentDeformationChain.value R h2 n nu j A U V f g h hH T hProper).
Local Notation Slice:=(@CartesianSlice.value R h2 1%N n 1%N j AT U hAT hU S).

(** Source for [current_deformation_chain_test_action]:
    the literal h#([0,1] times T) is T applied
    to any compact representative of K_h omega,
    by 4.1.8–9, pp. 360–363, as required
    by 4.1.18, p. 374. *)
Theorem current_deformation_chain_test_action (omega:DV) (beta:DU):
  @is_current_homotopy_test_replacement R h2 n nu j j A U V f g h hH T
    (Inc omega) beta ->
  @current_value R h2 nu V hV (1+j)%N chain omega=
    @current_value R h2 n U hU j T beta.
Proof.
move=>[Wbeta [hWbeta [hTWbeta [hWbetaU hBeta]]]].
have[lambda [O [hO [hPO [hOAU hLambda]]]]]:=
  @current_pushforward_test_replacement_exists R h2 (1+n)%N nu (1+j)%N
    AU V hAU hV P h image hH.2 properP omega.
rewrite current_deformation_chain_pushforward
  (@CurrentPushforward.laws R h2 (1+n)%N nu (1+j)%N AU V hAU hV P h image hH.2 properP
    omega lambda (ex_intro _ O (conj hO (conj hPO (conj hOAU hLambda)))))
  current_cartesian_product_action.
apply:(@current_test_local_support_values_equal R h2 n j U hU T (Slice lambda) beta)=>x hx.
have [Q [W [OQ [hW [hxW [hWU [hOQ [hKQ [hOQAU [hQ hSlice]]]]]]]]]]:=
  @current_homotopy_transgression_local_test R h2 n nu j A U V f g h hH x hx.1.
have hCompactS:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R 1%N)))
    (@current_support R h2 1%N AT hAT 1%N S).
  exact:(@current_support_compact_bound R h2 1%N 1%N AT hAT KTime S
    (@oriented_segment_current_support R h2 1%N AT hAT
      (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) hSegment)).
have hParameter a (ha:@current_support R h2 1%N AT hAT 1%N S a):
    (O `&` OQ) (euclidean_block_join (a,x)).
  split;last exact:hKQ a (@oriented_segment_current_support R h2 1%N AT hAT
    (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) hSegment a ha).
  apply:hPO.
  rewrite current_cartesian_support.
  change (@current_support R h2 1%N AT hAT 1%N S
      ((@euclidean_block_split R 1%N n (euclidean_block_join (a,x))).1) /\
    @current_support R h2 n U hU j T
      ((@euclidean_block_split R 1%N n (euclidean_block_join (a,x))).2)).
  by rewrite euclidean_block_joinK.
have [D [hD [hxD [hDU hMatch]]]]:=
  @current_cartesian_slice_near_support R h2 1%N n 1%N j AT U hAT hU S hCompactS
    lambda (Q (Inc omega)) x hx.1 (O `&` OQ) (openI hO hOQ) hParameter
    (fun y hy=>eq_trans (hLambda y hy.1) (esym (hQ (Inc omega) y hy.2))).
exists ((D `&` W) `&` Wbeta);split;first exact:openI (openI hD hW) hWbeta.
split;first exact:conj (conj hxD hxW) (hTWbeta x hx).
move=>y [[hyD hyW] hyBeta].
rewrite (hMatch y hyD) (hSlice (Inc omega) y hyW).
exact:esym (hBeta y hyBeta).
Qed.
End CurrentDeformationChainTestAction.
