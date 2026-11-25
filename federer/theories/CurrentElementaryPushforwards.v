(** Federer (1969), 4.1.10, p. 364: identity pushforward
    fixes T, constant pushforward is zero in positive degree, and
    is T(1)delta_u in degree zero. Currents have compact support;
    no representation or finite-mass hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero CurrentSpaces CurrentEvaluation CurrentProperSupport
  CurrentPushforwardSealed CurrentCompactSmoothValue CurrentCompactPushforwardTests
  CurrentElementaryPullbacks CurrentConstantZeroPullback CurrentConstantFields CurrentDirac
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentElementaryPushforwards.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.

(** Source for [current_compact_identity_pushforward]: g#T=T
    for the identity g and every compactly supported T, Federer
    4.1.10, p. 364, including its original arbitrary-open extension. *)
Theorem current_compact_identity_pushforward j
    (T : @current_space R h2 n U hU j)
    (hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU j T))
    (hImage : forall x, U x -> U x)
    (hId : norm_class_all_orders hNX hNX U (fun x:X => x))
    (hProper : @is_current_proper_on_support R h2 n n j U hU U T (fun x:X => x) hImage) :
  @CurrentPushforward.value R h2 n n j U U hU hU T (fun x:X => x) hImage hId hProper=T.
Proof.
apply: current_values_extensional => psi.
rewrite (@current_compact_pushforward_test_value R h2 n n j U U hU hU
  (fun x:X => x) hImage hId T hProper hCompact psi) current_identity_pullback.
exact: current_compact_smooth_test_value.
Qed.

(** Source for [current_compact_constant_positive_pushforward]:
    f#T=0 for the constant map f=u and positive degree, Federer
    4.1.10, p. 364. Only compact support of the original T is used. *)
Theorem current_compact_constant_positive_pushforward j (V : set X)
    (hV : forall x, V x -> norm_domain_interior NX V x) (u : X)
    (T : @current_space R h2 n U hU j.+1)
    (hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU j.+1 T))
    (hImage : forall x, U x -> V u)
    (hConst : norm_class_all_orders hNX hNX U (fun _:X => u))
    (hProper : @is_current_proper_on_support R h2 n n j.+1 U hU V T (fun _:X => u) hImage) :
  @CurrentPushforward.value R h2 n n j.+1 U V hU hV T (fun _:X => u) hImage hConst hProper=0.
Proof.
apply: current_values_extensional => psi.
rewrite (@current_compact_pushforward_test_value R h2 n n j.+1 U V hU hV
  (fun _:X => u) hImage hConst T hProper hCompact psi) current_constant_positive_pullback linear0.
by rewrite (linear0 (@current_value R h2 n V hV j.+1)) hom_zeroE.
Qed.

(** Source for [current_compact_constant_zero_pushforward]:
    f#T=T(1)delta_u in degree zero, Federer 4.1.10, p. 364.
    T(1) is the existing unique smooth-dual extension on the
    actual scalar one. The target may be any original open V. *)
Theorem current_compact_constant_zero_pushforward (V : set X)
    (hV : forall x, V x -> norm_domain_interior NX V x) (u : X)
    (T : @current_space R h2 n U hU 0%N)
    (hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU 0%N T))
    (hImage : forall x, U x -> V u)
    (hConst : norm_class_all_orders hNX hNX U (fun _:X => u))
    (hProper : @is_current_proper_on_support R h2 n n 0%N U hU V T (fun _:X => u) hImage) :
  @CurrentPushforward.value R h2 n n 0%N U V hU hV T (fun _:X => u) hImage hConst hProper=
    @current_compact_total R h2 n U hU T hCompact *: @dirac_current R h2 n V hV u.
Proof.
apply: current_values_extensional => psi.
rewrite (@current_compact_pushforward_test_value R h2 n n 0%N U V hU hV
  (fun _:X => u) hImage hConst T hProper hCompact psi) current_constant_zero_pullback linearZ.
rewrite linearZ hom_scaleE dirac_current_evaluation.
change (zero_form_value (@current_test_value R h2 n V hV 0%N psi u)*
  @current_compact_total R h2 n U hU T hCompact=
  @current_compact_total R h2 n U hU T hCompact*
    zero_form_value (@current_test_value R h2 n V hV 0%N psi u)).
exact: mulrC.
Qed.
End CurrentElementaryPushforwards.
