(** Federer (1969), 4.1.18, p. 374: compact
    kernel parameters make h(t,z,x)=x+t z proper
    on [0,1] times every closed carrying set with
    bounded z. The x support may be noncompact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology
  NormDifferentialUP NormOpenDomainLaws NormFiniteLinearBound NormRegularity
  NormClassZeroWhole NormClassZeroTopology NormCompactFunctionBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockLinearMaps
  EuclideanCartesianMap CurrentCartesianCompact CurrentCompactTimeCylinder
  ScalarCurrentIntervalCompact FiniteNormMetricCompactness SmoothCompactSet
  CurrentProperOnContainingSet CurrentContainingCompactCriterion
  CurrentTranslationParameterHomotopy ProperMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanTranslationCylinderProper.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)).
Local Notation P:=(R_n R (1+(n+n))%N).
Local Notation N k:=(inner_norm (@euclidean_inner_productP R k)).
Local Notation hN k:=(inner_norm_real_norm (@euclidean_inner_productP R k)).
Local Notation XT:=(real_norm_metric_space (hN n)).
Local Notation ZT:=(real_norm_metric_space (hN (n+n)%N)).
Local Notation PT:=(real_norm_metric_space (hN (1+(n+n))%N)).
Local Notation TT:=(real_norm_metric_space (hN 1%N)).
Local Notation FullP:=(fun _:P=>True).
Local Notation FullX:=(fun _:X=>True).
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation pt:=(@euclidean_first_block_map R 1%N (n+n)%N).
Local Notation qt:=(@euclidean_last_block_map R 1%N (n+n)%N).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Variable C:set Z.
Hypothesis hClosed:@closed ZT C.
Variable epsilon:R.
Hypothesis hEpsilon:0<=epsilon.
Hypothesis hBound:forall a,C a->N n (p a)<=epsilon.
Local Notation Cylinder:=(@current_compact_time_cylinder_carrier R (n+n)%N C).

(** Source for [euclidean_translation_parameter_cylinder_proper]:
    the original translation homotopies are proper uniformly
    on every compact kernel parameter set, supporting
    Federer 4.1.18, p. 374. This proof uses
    |x|<=|x+t z|+epsilon, not a false compactness
    assumption on the original x support. *)
Theorem euclidean_translation_parameter_cylinder_proper:
  is_proper_map (@current_map_on_containing_set R (1+(n+n))%N n
    FullP FullX Cylinder (fun _ _=>Logic.I) H (fun _ _=>Logic.I)).
Proof.
have hPT:continuous (fun y:PT=>(pt y:TT)).
  apply:norm_bounded_linear_continuous.
  exact:(@norm_finite_linear_bounded R P (R_n R 1%N)
    (N (1+(n+n))%N) (N 1%N) (hN (1+(n+n))%N) (hN 1%N)
    (1+(n+n))%N (@coordinate_basis R (1+(n+n))%N)
    (@coordinate_basisP R (1+(n+n))%N) pt).
have hQT:continuous (fun y:PT=>(qt y:ZT)).
  apply:norm_bounded_linear_continuous.
  exact:(@norm_finite_linear_bounded R P Z
    (N (1+(n+n))%N) (N (n+n)%N) (hN (1+(n+n))%N) (hN (n+n)%N)
    (1+(n+n))%N (@coordinate_basis R (1+(n+n))%N)
    (@coordinate_basisP R (1+(n+n))%N) qt).
have hBand:@closed TT [set a|0<=@euclidean_one_project R a<=1].
  apply:compact_closed;first exact:metric_hausdorff.
  exact:(@scalar_current_closed_interval_compact R 0 1).
have hCylinder:@closed PT Cylinder.
  apply:closedI.
  - apply:preimage_closed hBand=>y _;exact:hPT y.
  - apply:preimage_closed hClosed=>y _;exact:hQT y.
have hH:continuous (fun y:PT=>(H y:XT)).
  move=>y;apply:(@norm_class_zero_continuous_at R P X
    (N (1+(n+n))%N) (N n) (hN (1+(n+n))%N) (hN n)
    FullP H y (norm_class_continuous
      (@current_translation_parameter_homotopy_smooth_whole R n 0%N))).
  exact:Logic.I.
apply:current_containing_compact_loci_proper=>K.
have hKClosed:@closed XT (smooth_compact_carrier K).
  exact:compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K).
have hFibreClosed:@closed PT [set y|Cylinder y /\smooth_compact_carrier K (H y)].
  apply:closedI hCylinder _.
  apply:preimage_closed hKClosed=>y _;exact:hH y.
have hId:continuous (fun x:XT=>x) by move=>x;exact:cvg_id.
have [M [hM hKBound]]:=@norm_class_zero_compact_bounded R X X (N n) (N n)
  (hN n) (hN n) setT (smooth_compact_carrier K) (fun x=>x)
  (smooth_compact_is_compact K) (fun _ _=>Logic.I)
  (norm_continuous_whole_class_zero hId).
pose BZ:set XT:=[set z|N n z<=epsilon].
pose BX:set XT:=[set x|N n x<=M+epsilon].
have hBZ:compact BZ:=@finite_norm_metric_ball_compact R X (N n) (hN n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) epsilon.
have hBX:compact BX:=@finite_norm_metric_ball_compact R X (N n) (hN n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (M+epsilon).
have hRectangle:@compact ZT (@euclidean_cartesian_set R n n BZ BX).
  exact:current_cartesian_compact hBZ hBX.
have hCompact:=@current_compact_time_cylinder_is_compact R (n+n)%N
  (@euclidean_cartesian_set R n n BZ BX) hRectangle.
apply:(@subclosed_compact PT _ _ hFibreClosed hCompact)=>y [[ht hCy] hKy].
split;first exact:ht.
split;first exact:hBound _ hCy.
pose t:=@euclidean_one_project R (pt y).
have hT:0<=t<=1:=ht.
have hAbs:`|t|<=1 by rewrite (ger0_norm (andP hT).1);exact:(andP hT).2.
have hNZ:0<=N n (p (qt y)):=real_seminorm_nonnegative (hN n).1 _.
have hScale:N n (t*:p (qt y))<=epsilon.
  rewrite (real_seminorm_scale (hN n).1).
  have hSmall:=ler_wpM2r hNZ hAbs.
  rewrite mul1r in hSmall.
  exact:le_trans hSmall (@hBound (qt y) hCy).
have hTriangle:=real_seminorm_triangle (hN n).1 (H y) (-(t*:p (qt y))).
rewrite current_translation_parameter_homotopy_coordinates
  addrK (real_seminorm_negate (hN n).1) in hTriangle.
have hImage:=@hKBound (H y) hKy.
rewrite current_translation_parameter_homotopy_coordinates in hImage.
exact:le_trans hTriangle (lerD hImage hScale).
Qed.
End EuclideanTranslationCylinderProper.
