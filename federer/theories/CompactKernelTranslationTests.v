(** Federer (1969), 4.1.18, p. 374: a single
    genuine compact product test agrees with the
    original addition pullback on the whole compact
    kernel strip, for every spatial x. This proves
    the literal current translation average for arbitrary
    current supports.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassZeroWhole NormCompactFunctionBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap AlternatingForms CurrentSpaces CurrentCartesianDomain CurrentCartesianCompact
  SmoothCompactSet FiniteNormMetricCompactness SmoothPullbackCutoffTests
  SmoothFormPullbackSealed SmoothFunctionSupport
  CurrentTranslationParameterHomotopy CurrentAdditionZeroFactorPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactKernelTranslationTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation Add:=(@current_translation_parameter_end R n).
Local Notation Image:=(fun (z:Z) (_:AB z)=>Logic.I).
Local Notation hAdd:=(@current_addition_product_smooth R n).
Local Notation E:=(@current_smooth_space R h2 n Full hFull j).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull j).
Local Notation F:=(@current_smooth_space R h2 (n+n)%N AB hAB j).
Local Notation fv:=(@current_smooth_value R h2 (n+n)%N AB hAB j).
Local Notation DC:=(@current_test_space R h2 (n+n)%N AB hAB j).
Local Notation tv:=(@current_test_value R h2 (n+n)%N AB hAB j).
Local Notation Pull:=(@SmoothFormPullback.operator R h2 (n+n)%N n j AB Full hAB hFull
  Add Image hAdd).
Variable epsilon:R.
Hypothesis hEpsilon:0<=epsilon.

(** Source for [compact_kernel_translation_tests]: original
    compact target support and compact kernel support
    give one actual linear compact replacement on the
    whole kernel strip, supporting 4.1.18, p. 374.
    No compactness assumption on T is involved. *)
Theorem compact_kernel_translation_tests (K:smooth_compact_set hNX Full):
  exists Q:Hom E DC,forall omega:E,
    @smooth_function_support R X (A_m X R^o j) NX hNX Full E ev omega `<=` smooth_compact_carrier K ->
    forall z x,NX z<=epsilon ->tv (Q omega) (euclidean_block_join (z,x))=
      fv (Pull omega) (euclidean_block_join (z,x)).
Proof.
have hIdentity:continuous (fun x:XT=>x) by move=>x;exact:cvg_id.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X NX NX hNX hNX
  setT (smooth_compact_carrier K) (fun x=>x) (smooth_compact_is_compact K)
  (fun _ _=>Logic.I) (norm_continuous_whole_class_zero hIdentity).
pose C:set Z:=[set y|NX (p y)<=epsilon].
pose B0:set XT:=[set z|NX z<=epsilon].
pose B1:set XT:=[set x|NX x<=M+epsilon].
have hB0:compact B0:=@finite_norm_metric_ball_compact R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) epsilon.
have hB1:compact B1:=@finite_norm_metric_ball_compact R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) (M+epsilon).
pose L:=@Build_smooth_compact_set R Z NZ hNZ AB
  (@euclidean_cartesian_set R n n B0 B1) (fun _ _=>conj Logic.I Logic.I)
  (@current_cartesian_compact R n n B0 B1 hB0 hB1).
have hLocus y:C y->smooth_compact_carrier K (Add y)->smooth_compact_carrier L y.
  move=>hy hKy;split;first exact:hy.
  have hTriangle:=real_seminorm_triangle hNX.1 (Add y) (-(p y)).
  have hAddValue:Add y=q y+p y by rewrite /current_translation_parameter_end hom_addE.
  rewrite hAddValue addrK (real_seminorm_negate hNX.1) in hTriangle.
  exact:le_trans hTriangle (lerD (hBound _ hKy) hy).
have [Q [_ [W [hW [hCW [hWAB hQ]]]]]]:=
  @smooth_pullback_compact_locus_tests R h2 (n+n)%N n j AB Full hAB hFull C
    (fun _ _=>conj Logic.I Logic.I) Add Image hAdd K L hLocus.
exists Q=>omega hOmega z x hz.
apply:(@hQ omega hOmega (euclidean_block_join (z,x))).
apply:hCW.
change (is_true (NX ((@euclidean_block_split R n n (euclidean_block_join (z,x))).1)<=epsilon)).
by rewrite euclidean_block_joinK.
Qed.
End CompactKernelTranslationTests.
