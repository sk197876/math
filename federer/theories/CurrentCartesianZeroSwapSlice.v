(** Federer (1969), 4.1.18, p. 374: after
    the original Cartesian interchange, a zero-degree
    kernel factor extracts exactly the original
    spatial form coefficient. Every equal-degree
    identification remains explicit.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianSwap EuclideanCartesianSwapLinear
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts ExteriorMapScaling
  AlternatingForms AlternatingDual AlternatingPairing CurrentSpaces CurrentDiracDensity
  CurrentZeroDegreeExteriorLaws CurrentDegreeTransport CurrentCartesianDomain
  CurrentCartesianSwapDomain CurrentCartesianSwapTests CurrentCartesianSliceTestSealed
  CurrentCartesianSliceTestPairing CurrentCartesianVectorProduct
  SmoothFormPullbackUP SmoothFormPullbackSealed SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_pairing_degree_reindex]: exact
    pairing under equal natural degree identifications,
    supporting the zero-factor interchange in Federer
    4.1.18, p. 374. *)
Lemma current_pairing_degree_reindex (K:fieldType) (V:lmodType K)
    a b (e:a=b) (xi:exterior_power V a) (phi:A_m V K^o b):
  @pairing K V K^o b (@exterior_reindex K V a b e xi) phi=
    @pairing K V K^o a xi (@form_reindex K V K^o b a (esym e) phi).
Proof.
by case: b / e in phi *.
Qed.

(** Source for [current_exterior_map_degree_reindex]: the
    old exterior map preserves exact equal-degree
    identifications, supporting 4.1.18, p. 374. *)
Lemma current_exterior_map_degree_reindex (K:fieldType) (V W:lmodType K)
    (L:{linear V->W}) a b (e:a=b) (xi:exterior_power V a):
  exterior_reindex e (exterior_power_map L a xi)=
    exterior_power_map L b (exterior_reindex e xi).
Proof.
by case:b/e.
Qed.

Section CurrentCartesianZeroSwapSlice.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation DC:=(fun d=>@current_test_space R h2 (n+n)%N AB hAB d).
Local Notation EC:=(fun d=>@current_smooth_space R h2 (n+n)%N AB hAB d).
Local Notation evC:=(fun d=>@current_smooth_value R h2 (n+n)%N AB hAB d).
Local Notation value:=(fun d=>@current_test_value R h2 (n+n)%N AB hAB d).
Local Notation hEC:=(fun d=>@current_smooth_space_laws R h2 (n+n)%N AB hAB d).
Local Notation P:=(@euclidean_first_injection_map R n n).
Local Notation Q:=(@euclidean_last_injection_map R n n).
Local Notation swap:=(@euclidean_cartesian_swap_map R n n).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Local Notation e:=(esym (addnC j 0%N)).
Local Notation Reverse:=(fun phi:DC j=>
  @current_cartesian_swap_tests R h2 n n (j+0)%N Full Full hFull hFull
    (@current_test_degree_transport R h2 (n+n)%N AB hAB j (j+0)%N e phi)).

(** Source for [current_cartesian_zero_swap_slice_pairing]:
    the reversed first-variable compact test has exactly
    the coefficient of the original zero-first-factor
    test, supporting the scalar integral/current exchange
    of Federer 4.1.18, p. 374. *)
Theorem current_cartesian_zero_swap_slice_pairing (phi:DC j) z x
    (eta:exterior_power X j):
  pairing eta (@current_test_value R h2 n Full hFull j
    (@CartesianSliceTest.value R h2 n n Full Full hFull hFull j 0%N
      z Logic.I unit (Reverse phi)) x)=
  pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
    (value j phi (euclidean_block_join (z,x))).
Proof.
rewrite (@current_cartesian_slice_test_pairing R h2 n n j 0%N Full Full hFull hFull
  z Logic.I unit (Reverse phi) x Logic.I eta).
change (pairing (@current_cartesian_vector_product R n n j 0%N eta unit)
  (evC (j+0)%N
    (smooth_test_inclusion (hEC (j+0)%N) (Reverse phi))
    (euclidean_block_join (x,z)))=
  pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
    (value j phi (euclidean_block_join (z,x)))).
rewrite current_cartesian_swap_tests_inclusion.
have hPoint:AB (euclidean_block_join (x,z)) by split.
rewrite (@smooth_form_pullback_values R (n+n)%N (n+n)%N (j+0)%N AB AB _ _
  (evC (j+0)%N) (evC (j+0)%N) swap _
  (@SmoothFormPullback.laws R h2 (n+n)%N (n+n)%N (j+0)%N AB AB hAB hAB swap
    (fun z hz=>@current_cartesian_swap_image R n n Full Full z hz)
    (@euclidean_cartesian_swap_smooth R n n AB hAB))
  (smooth_test_inclusion (hEC (j+0)%N)
    (@current_test_degree_transport R h2 (n+n)%N AB hAB j (j+0)%N e phi))
  (euclidean_block_join (x,z)) swap hPoint
  (@euclidean_cartesian_swap_differential R n n AB hAB _ hPoint)).
have hValue:=@current_test_degree_transport_values R h2 (n+n)%N AB hAB
  j (j+0)%N e phi (swap (euclidean_block_join (x,z))).
change (evC (j+0)%N
  (smooth_test_inclusion (hEC (j+0)%N)
    (@current_test_degree_transport R h2 (n+n)%N AB hAB j (j+0)%N e phi))
  (swap (euclidean_block_join (x,z)))=
  form_reindex e (value j phi (swap (euclidean_block_join (x,z))))) in hValue.
rewrite hValue A_m_dual_pairing.
have hSwapPoint:swap (euclidean_block_join (x,z))=euclidean_block_join (z,x).
  change (euclidean_block_join
    ((euclidean_block_split (euclidean_block_join (x,z))).2,
      (euclidean_block_split (euclidean_block_join (x,z))).1)=euclidean_block_join (z,x)).
  by rewrite euclidean_block_joinK.
rewrite hSwapPoint.
have hProof:e=esym (addn0 j):=Prop_irrelevance _ _.
rewrite hProof -current_pairing_degree_reindex current_exterior_map_degree_reindex.
rewrite /current_cartesian_vector_product /current_scalar_multivector_unit
  !exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_right scale1r
  exterior_power_map_composition.
have hComposition:linear_comp (hom_as_linear swap) (hom_as_linear P)=1 (hom_as_linear Q).
  move=>v.
  change (euclidean_block_join
    (@euclidean_last_block R n n (@euclidean_first_injection R n n v),
      @euclidean_first_block R n n (@euclidean_first_injection R n n v))=
    @euclidean_last_injection R n n v).
  by rewrite euclidean_last_block_first_injection euclidean_first_block_injectionK.
rewrite (@exterior_power_map_ext R X Z
  (linear_comp (hom_as_linear swap) (hom_as_linear P)) (hom_as_linear Q)
  hComposition j eta) exterior_product_zeroth_scalar_left scale1r.
reflexivity.
Qed.
End CurrentCartesianZeroSwapSlice.
