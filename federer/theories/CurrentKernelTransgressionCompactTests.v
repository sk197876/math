(** Federer (1969), 4.1.18, p. 374: one
    compact test replacement computes the parameter
    transgression near the entire compact-kernel strip.
    The spatial bound comes from the original
    x+t z formula and the compact target support;
    no compactness of T is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom AlternatingForms RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassZeroWhole NormCompactFunctionBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentSpaces CurrentCartesianCompact SmoothCompactSet FiniteNormMetricCompactness
  SmoothFunctionSupport CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentSegmentCompactSet ScalarSegmentCoordinateValues
  CurrentHomotopyAvoidCompact CurrentHomotopyTransgressionSealed
  CurrentHomotopyCarrierCompactTests CurrentTranslationParameterHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentKernelTransgressionCompactTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+n)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n)%N)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation FullZ:=(fun _:Z=>True).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation F:=(@current_smooth_space R h2 n Full hTarget (1+m)%N).
Local Notation fv:=(@current_smooth_value R h2 n Full hTarget (1+m)%N).
Local Notation D:=(@current_test_space R h2 (n+n)%N FullZ hSource m).
Local Notation value:=(@current_test_value R h2 (n+n)%N FullZ hSource m).
Local Notation ev:=(@current_smooth_value R h2 (n+n)%N FullZ hSource m).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 (n+n)%N n m
  (fun _=>True) FullZ Full q End H hH).
Variable epsilon:R.
Hypothesis hEpsilon:0<=epsilon.
Local Notation Strip:=[set a:Z|NX (p a)<=epsilon].

(** Source for [current_kernel_transgression_compact_tests]:
    the original averaged-transgression action admits a
    common compact replacement near the entire kernel
    strip, supporting 4.1.18, p. 374. *)
Theorem current_kernel_transgression_compact_tests (K:smooth_compact_set hNX Full):
  exists Q:Hom F D,exists W:set Z,@open (real_norm_metric_space hNZ) W /\
    Strip `<=` W /\
    forall omega:F,@smooth_function_support R X (A_m X R^o (1+m)%N) NX hNX Full F fv omega `<=`
      smooth_compact_carrier K ->
      forall a,W a->value (Q omega) a=ev (KH omega) a.
Proof.
have hIdentity:continuous (fun x:XT=>x) by move=>x;exact:cvg_id.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X NX NX hNX hNX
  setT (smooth_compact_carrier K) (fun x=>x) (smooth_compact_is_compact K)
  (fun _ _=>Logic.I) (norm_continuous_whole_class_zero hIdentity).
pose B0:set XT:=[set z|NX z<=epsilon].
pose B1:set XT:=[set x|NX x<=M+epsilon].
have hB0:compact B0:=@finite_norm_metric_ball_compact R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) epsilon.
have hB1:compact B1:=@finite_norm_metric_ball_compact R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) (M+epsilon).
pose L:=@Build_smooth_compact_set R Z NZ hNZ FullZ
  (@euclidean_cartesian_set R n n B0 B1) (fun _ _=>Logic.I)
  (@current_cartesian_compact R n n B0 B1 hB0 hB1).
pose Avoid:=@current_homotopy_avoid_compact R (n+n)%N n (fun _=>True)
  FullZ Full q End H hH.1 K.
have hCover:Strip `<=` (smooth_compact_carrier L `|` Avoid).
  move=>a ha;case:(pselect (smooth_compact_carrier L a))=>[hL|hL];first by left.
  right;split;first exact:Logic.I.
  move=>s hs hImage.
  pose hInterval:=@current_homotopy_parameter_interval R (n+n)%N n
    (fun _=>True) FullZ Full q End H hH.1.
  pose hSegment:=@current_homotopy_time_segment_domain R (fun _=>True) hInterval.
  have[t [ht hS]]:=@current_segment_compact_points R 1%N
    (@current_homotopy_time_domain R (fun _=>True))
    (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) hSegment s hs.
  have hTime:0<=@euclidean_one_project R s<=1.
    rewrite hS scalar_segment_parameter_value subr0 mul1r addr0 euclidean_one_embedK.
    by move:ht;rewrite in_itv /=.
  pose time:=@euclidean_one_project R s.
  have hPoint:H (euclidean_block_join (s,a))=q a+time*:p a.
    rewrite current_translation_parameter_homotopy_coordinates.
    change (q ((@euclidean_block_split R 1%N (n+n)%N (euclidean_block_join (s,a))).2)+
      @euclidean_one_project R
        ((@euclidean_block_split R 1%N (n+n)%N (euclidean_block_join (s,a))).1)*:
        p ((@euclidean_block_split R 1%N (n+n)%N (euclidean_block_join (s,a))).2)=
      q a+time*:p a).
    by rewrite euclidean_block_joinK.
  have hScale:NX (time*:p a)<=epsilon.
    rewrite inner_normZ (ger0_norm (andP hTime).1).
    have h:=ler_wpM2r (inner_norm_nonnegative (@euclidean_inner_productP R n) (p a))
      (andP hTime).2.
    rewrite mul1r in h;exact:le_trans h ha.
  have hTriangle:=real_seminorm_triangle hNX.1
    (H (euclidean_block_join (s,a))) (-(time*:p a)).
  rewrite hPoint addrK (real_seminorm_negate hNX.1) in hTriangle.
  have hSpatial:NX (q a)<=M+epsilon.
    have hAt:=hBound (H (euclidean_block_join (s,a))) hImage.
    rewrite hPoint in hAt.
    exact:le_trans hTriangle (lerD hAt hScale).
  apply:hL;exact:conj ha hSpatial.
have[Q [W [hW [hStrip [hWDomain hQ]]]]]:=
  @current_homotopy_carrier_compact_tests R h2 (n+n)%N n m
    (fun _=>True) FullZ Full q End H hH K L Strip hCover.
exists Q,W;by split=>//;split.
Qed.
End CurrentKernelTransgressionCompactTests.
