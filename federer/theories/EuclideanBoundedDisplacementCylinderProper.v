(** Federer (1969), 4.1.18, p. 374: the
    original translation homotopy is proper on the
    closed cylinder over any closed support, because
    its displacement there is bounded. The support
    need not be compact.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology
  NormDifferentialUP NormFiniteLinearBound NormClassZeroWhole NormCompactFunctionBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockLinearMaps CurrentCompactTimeCylinder
  ScalarCurrentIntervalCompact FiniteNormMetricCompactness SmoothCompactSet
  CurrentProperOnContainingSet CurrentContainingCompactCriterion ProperMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanBoundedDisplacementCylinderProper.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation P:=(R_n R (1+n)%N).
Local Notation N k:=(inner_norm (@euclidean_inner_productP R k)).
Local Notation hN k:=(inner_norm_real_norm (@euclidean_inner_productP R k)).
Local Notation XT:=(real_norm_metric_space (hN n)).
Local Notation PT:=(real_norm_metric_space (hN (1+n)%N)).
Local Notation TT:=(real_norm_metric_space (hN 1%N)).
Local Notation p:=(@euclidean_first_block_map R 1%N n).
Local Notation q:=(@euclidean_last_block_map R 1%N n).
Variable C:set X.
Hypothesis hClosed:@closed XT C.
Variable H:P->X.
Hypothesis hContinuous:continuous (fun y:PT=>(H y:XT)).
Variable epsilon:R.
Hypothesis hBound:forall y,@current_compact_time_cylinder_carrier R n C y->
  N n (H y-q y)<=epsilon.
Local Notation Cylinder:=(@current_compact_time_cylinder_carrier R n C).

(** Source for [euclidean_bounded_displacement_cylinder_proper]:
    bounded displacement on the literal closed
    support cylinder proves its properness, by
    2.2.17 and compact Euclidean balls, supporting
    the original h_z in 4.1.18, p. 374. *)
Theorem euclidean_bounded_displacement_cylinder_proper:
  is_proper_map (@current_map_on_containing_set R (1+n)%N n
    (fun _=>True) (fun _=>True) Cylinder (fun _ _=>Logic.I) H (fun _ _=>Logic.I)).
Proof.
have hP:continuous (fun y:PT=>(p y:TT)).
  apply:norm_bounded_linear_continuous.
  exact:(@norm_finite_linear_bounded R P (R_n R 1%N) (N (1+n)%N) (N 1%N)
    (hN (1+n)%N) (hN 1%N) (1+n)%N (@coordinate_basis R (1+n)%N)
    (@coordinate_basisP R (1+n)%N) p).
have hQ:continuous (fun y:PT=>(q y:XT)).
  apply:norm_bounded_linear_continuous.
  exact:(@norm_finite_linear_bounded R P X (N (1+n)%N) (N n)
    (hN (1+n)%N) (hN n) (1+n)%N (@coordinate_basis R (1+n)%N)
    (@coordinate_basisP R (1+n)%N) q).
have hBand:@closed TT [set t|0<=@euclidean_one_project R t<=1].
  exact:compact_closed (@metric_hausdorff R TT) (@scalar_current_closed_interval_compact R 0 1).
have hCylinder:@closed PT Cylinder.
  apply:closedI.
  - apply:preimage_closed hBand=>y _;exact:hP y.
  - apply:preimage_closed hClosed=>y _;exact:hQ y.
apply:current_containing_compact_loci_proper=>K.
have hTargetClosed:@closed XT (smooth_compact_carrier K).
  exact:compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K).
have hFibreClosed:@closed PT [set y|Cylinder y /\smooth_compact_carrier K (H y)].
  apply:closedI hCylinder _.
  apply:preimage_closed hTargetClosed=>y _;exact:hContinuous y.
have hIdentity:continuous (fun x:XT=>x) by move=>x;exact:cvg_id.
have [M [hM hKBound]]:=@norm_class_zero_compact_bounded R X X (N n) (N n)
  (hN n) (hN n) setT (smooth_compact_carrier K) (fun x=>x)
  (smooth_compact_is_compact K) (fun _ _=>Logic.I)
  (norm_continuous_whole_class_zero hIdentity).
pose B:set XT:=[set x|N n x<=M+epsilon].
have hB:compact B:=@finite_norm_metric_ball_compact R X (N n) (hN n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (M+epsilon).
have hCompact:=@current_compact_time_cylinder_is_compact R n B hB.
apply:(@subclosed_compact PT _ _ hFibreClosed hCompact)=>y [hy hKy].
split;first exact:hy.1.
have hTriangle:=real_seminorm_triangle (hN n).1 (H y) (-(H y-q y)).
rewrite subKr (real_seminorm_negate (hN n).1) in hTriangle.
have hImageBound:N n (H y)<=M:=@hKBound (H y) hKy.
have hDisplacement:N n (H y-q y)<=epsilon:=@hBound y hy.
exact:le_trans hTriangle (lerD hImageBound hDisplacement).
Qed.
End EuclideanBoundedDisplacementCylinderProper.
