(** Federer (1969), 4.1.9, p. 363: the point current
    in the form-identity argument has support in its original
    singleton. The assertion includes a zero multivector, when
    the support may be empty. Reuse the original compact
    support criterion from 4.1.7, pp. 355–359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry SmoothCompactSet SmoothFunctionSupport
  PointMultivectorCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PointMultivectorCurrentSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation Form := (A_m X R^o j).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall y,U y->norm_domain_interior NX U y.
Variable x:X.
Hypothesis hx:U x.
Local Notation K := (@smooth_compact_singleton R X NX hNX U x hx).
Local Notation P := (@PointMultivectorCurrent.value R h2 n j U hU x hx).
Local Notation DT := (@current_test_space R h2 n U hU j).
Local Notation value := (@current_test_value R h2 n U hU j).
Local Notation action := (@current_value R h2 n U hU j).
Local Notation support := (@current_support R h2 n U hU j).

(** Source for [point_multivector_current_support]: the current
    beta to <eta,beta(x)> is supported in {x}, supporting
    the passage to pointwise form identities in Federer
    4.1.9, p. 363. No nonzero-vector hypothesis is needed. *)
Theorem point_multivector_current_support eta:support (P eta) `<=` [set x].
Proof.
apply:(@current_support_compact_criterion R h2 n j U hU K (P eta)).2=>beta hBeta.
have hZero:value beta x=0.
  apply:contrapT=>hNo.
  have hSupport:=@smooth_function_nonzero_in_support R X Form NX hNX U DT value beta x hx hNo.
  exact:(hBeta x hSupport).2 (erefl x).
rewrite (@PointMultivectorCurrent.laws R h2 n j U hU x hx eta beta) hZero.
exact:(bil0r (@pairing_bilinear R X R^o j) eta).
Qed.

(** Source for [point_multivector_current_compact]: the original
    point current has compact support even for eta=0,
    supporting Federer 4.1.9, p. 363. *)
Theorem point_multivector_current_compact eta:
  @compact (real_norm_metric_space hNX) [set y|support (P eta) y].
Proof.
apply:(@current_support_compact_bound R h2 n j U hU K (P eta)).
move=>y hy.
have hAt:=@point_multivector_current_support eta y hy.
exact hAt.
Qed.
End PointMultivectorCurrentSupport.
