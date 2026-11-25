(** Federer (1969), 4.1.10, p. 364: compute pushforwards
    of compactly supported currents from the original smooth extension.
    This supporting test-action law reuses 4.1.7 and 4.1.9. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentProperSupport CurrentPushforwardSealed CurrentPushforwardNormality
  CurrentCompactSmoothValue CurrentCompactPushforwardSmooth SmoothFormPullbackSealed
  SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_compact_pushforward_test_value]: the action
    of f#T is the smooth extension of T on the actual pullback,
    supporting the endpoint computations in Federer 4.1.10, p. 364.
    Compact support is used; representation and finite mass are not. *)
Theorem current_compact_pushforward_test_value (R : realType) (h2 : (1+1:R)!=0)
    (v n j : nat) (U : set (R_n R v)) (V : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV : forall y, V y -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V y)
    (f : R_n R v -> R_n R n) (hImage : forall x, U x -> V (f x))
    (hf : norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (T : @current_space R h2 v U hU j)
    (hProper : @is_current_proper_on_support R h2 v n j U hU V T f hImage)
    (hCompact : @compact
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R v)))
      (@current_support R h2 v U hU j T))
    (psi : @current_test_space R h2 n V hV j) :
  @current_value R h2 n V hV j
    (@CurrentPushforward.value R h2 v n j U V hU hV T f hImage hf hProper) psi=
  @current_compact_smooth_value R h2 v j U hU T hCompact
    (@SmoothFormPullback.operator R h2 v n j U V hU hV f hImage hf
      (smooth_test_inclusion (@current_smooth_space_laws R h2 n V hV j) psi)).
Proof.
pose S := @CurrentPushforward.value R h2 v n j U V hU hV T f hImage hf hProper.
pose hS := @current_pushforward_compact_support R h2 v n U V hU hV f
  hImage hf j T hProper hCompact.
apply: (eq_trans (esym (@current_compact_smooth_test_value R h2 n j V hV S hS psi))).
exact: current_compact_pushforward_smooth_value.
Qed.
