(** Federer (1969), 4.1.18, p. 375: addition is
    proper on a bounded closed set of translation
    parameters. This is the support properness needed
    for the original average of translated Radon
    measures; the second factor is unbounded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormFiniteLinearBound NormBoundedLinearTopology NormClassZeroWhole NormCompactFunctionBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentDomain CurrentCartesianDomain
  CurrentCartesianCompact FiniteNormMetricCompactness IsotropyGroupTopology ProperMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanCompactParameterAddition.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R (n+n)%N).
Local Notation N k:=(inner_norm (@euclidean_inner_productP R k)).
Local Notation hN k:=(inner_norm_real_norm (@euclidean_inner_productP R k)).
Local Notation XT:=(real_norm_metric_space (hN n)).
Local Notation YT:=(real_norm_metric_space (hN (n+n)%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation CT:=(current_domain R (n+n)%N AB).
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation q:=(@euclidean_last_block_map R n n).

(** Source for [euclidean_parameter_addition]: the
    original map (z,x) to x+z underlying the
    translated measures in 4.1.18, pp. 374–375. *)
Definition euclidean_parameter_addition (y:CT):XT:=q (set_val y)+p (set_val y).

(** Source for [euclidean_parameter_strip]: the literal
    closed epsilon ball of translation parameters in
    the original product domain, supporting 4.1.18,
    p. 375. No spatial bound is imposed. *)
Definition euclidean_parameter_strip (r:R):set CT:=
  [set y|N n (p (set_val y))<=r].

(** Source for [euclidean_parameter_addition_continuous]:
    continuity of addition follows from the earlier
    finite-dimensional bounded linear laws, supporting
    the translated Radon average in 4.1.18, p. 375. *)
Theorem euclidean_parameter_addition_continuous:
  continuous euclidean_parameter_addition.
Proof.
pose L:Hom Y X:=q+p.
have hL:continuous (fun y:YT=>(L y:XT)).
  apply:norm_bounded_linear_continuous.
  exact:(@norm_finite_linear_bounded R Y X (N (n+n)%N) (N n)
    (hN (n+n)%N) (hN n) (n+n)%N (@coordinate_basis R (n+n)%N)
    (@coordinate_basisP R (n+n)%N) L).
move=>y;exact:(continuous_comp (@set_type_val_continuous YT AB y) (hL (set_val y))).
Qed.

(** Source for [euclidean_parameter_strip_closed]: the
    original closed parameter ball is closed in the
    actual product domain, supporting 4.1.18, p. 375. *)
Theorem euclidean_parameter_strip_closed r:closed (euclidean_parameter_strip r).
Proof.
have hP:continuous (fun y:YT=>(p y:XT)).
  apply:norm_bounded_linear_continuous.
  exact:(@norm_finite_linear_bounded R Y X (N (n+n)%N) (N n)
    (hN (n+n)%N) (hN n) (n+n)%N (@coordinate_basis R (n+n)%N)
    (@coordinate_basisP R (n+n)%N) p).
have hBall:@closed XT [set x|N n x<=r].
  exact:compact_closed (@metric_hausdorff R XT)
    (@finite_norm_metric_ball_compact R X (N n) (hN n)
      n (@coordinate_basis R n) (@coordinate_basisP R n) r).
apply:preimage_closed hBall=>y _.
exact:(continuous_comp (@set_type_val_continuous YT AB y) (hP (set_val y))).
Qed.

(** Source for [euclidean_parameter_addition_strip_proper]:
    a compact target and bounded translation parameter
    bound the original spatial coordinate by the triangle
    inequality. The original closed inverse locus is
    therefore compact, by 2.2.17, p. 72; this
    supports the Radon average of 4.1.18, p. 375. *)
Theorem euclidean_parameter_addition_strip_proper r:
  is_proper_map (fun y:set_type (euclidean_parameter_strip r)=>
    euclidean_parameter_addition (set_val y)).
Proof.
move=>K hK.
have hIdentity:continuous (fun x:XT=>x) by move=>x;exact:cvg_id.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X (N n) (N n)
  (hN n) (hN n) setT K (fun x=>x) hK (fun _ _=>Logic.I)
  (norm_continuous_whole_class_zero hIdentity).
pose B1:set XT:=[set z|N n z<=r].
pose B2:set XT:=[set x|N n x<=M+r].
have hB1:compact B1:=@finite_norm_metric_ball_compact R X (N n) (hN n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) r.
have hB2:compact B2:=@finite_norm_metric_ball_compact R X (N n) (hN n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (M+r).
pose B:set YT:=euclidean_cartesian_set B1 B2.
have hB:compact B:=@current_cartesian_compact R n n B1 B2 hB1 hB2.
have hBInside:B `<=` AB by move=>y _;split.
pose BActual:set CT:=set_val @^-1` B.
have hBActual:compact BActual:=@set_type_compact_preimage YT AB B hB hBInside.
pose L:set CT:=euclidean_parameter_strip r `&` (euclidean_parameter_addition @^-1` K).
have hClosed:closed L.
  apply:(@closedI CT (euclidean_parameter_strip r)
    (euclidean_parameter_addition @^-1` K)).
  - exact:euclidean_parameter_strip_closed.
  -
  apply:preimage_closed (compact_closed (@metric_hausdorff R XT) hK)=>y _.
  exact:euclidean_parameter_addition_continuous.
have hL:compact L.
  apply:(@subclosed_compact CT L BActual hClosed hBActual)=>y [hy hKy].
  split;first exact:hy.
  have hTriangle:=real_seminorm_triangle (hN n).1
    (euclidean_parameter_addition y) (-(p (set_val y))).
  have hValue:euclidean_parameter_addition y-p (set_val y)= q (set_val y).
    by rewrite /euclidean_parameter_addition addrK.
  rewrite hValue (real_seminorm_negate (hN n).1) in hTriangle.
  exact:le_trans hTriangle (lerD (hBound _ hKy) hy).
have hIn:L `<=` euclidean_parameter_strip r by move=>y hy;exact:hy.1.
have hPre:=@set_type_compact_preimage CT (euclidean_parameter_strip r) L hL hIn.
have hEqual:(fun y:set_type (euclidean_parameter_strip r)=>
      euclidean_parameter_addition (set_val y)) @^-1` K=
    (set_val @^-1` L:set (set_type (euclidean_parameter_strip r))).
  apply:funext=>y;apply:propext;split.
  - move=>hy;split;first exact:set_valP y.
    exact:hy.
  - by move=>[_ hy].
by rewrite hEqual.
Qed.
End EuclideanCompactParameterAddition.

Arguments euclidean_parameter_addition : clear implicits.
Arguments euclidean_parameter_strip : clear implicits.
