(** Federer (1969), 4.1.19, p. 377: localize
    the class-one weak-derivative argument on the original
    compact support of its smooth coefficient. Continuous
    forms with that compact carrier are bounded measurable
    on U, using the preceding compact-field laws. *)
From mathcomp Require Import functions all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroTopology NormCompactFunctionBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentDomain CurrentCoefficientNorms
  CurrentCoefficientCompleteness SmoothCompactSet IsotropyGroupTopology
  SubtypeCompactHausdorff CompactSupportFunctionUP
  CompactContinuousVectorFields CompactContinuousVectorMeasurable
  EuclideanOpenDomainMeasure FlatCochainRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_current_form_bounded]:
    the compact class-one replacement in the weak
    equation of Federer 4.1.19, p. 377,
    belongs to the literal bounded measurable form
    class. The source remains the original open U;
    compactness supplies the bound also when K is empty. *)
Theorem compact_continuous_current_form_bounded
    (R : realType) (h2 : (1+1:R)!=0) n d
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (phi : R_n R n -> A_m (R_n R n) R^o d) :
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (@current_form_comass R h2 n d) U phi ->
  (forall x, U x -> ~smooth_compact_carrier K x -> phi x=0) ->
  @is_bounded_measurable_current_form R h2 n U d
    (fun x : current_domain R n U => phi (set_val x)).
Proof.
move=> hPhi hOff.
pose X := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT := real_norm_metric_space hNX.
pose UT := current_domain R n U.
pose Y := A_m X R^o d.
pose N := @current_form_comass R h2 n d.
pose hN := @current_form_comass_real_norm R h2 n d.
pose f := fun x : UT => phi (set_val x).
pose C : set UT := set_val @^-1` smooth_compact_carrier K.
have hC : compact C := @set_type_compact_preimage XT U
  (smooth_compact_carrier K) (smooth_compact_is_compact K) (smooth_compact_in_domain K).
have hClosed : closed C := compact_closed
  (@set_type_hausdorff XT U (@metric_hausdorff R XT)) hC.
have hF : continuous (fun x : UT => (f x : real_norm_metric_space hN)).
  exact: (@norm_class_zero_restriction_continuous R X Y NX N hNX hN U phi hPhi).
have hNormOff (x : UT) (hx : ~C x) : N (f x)=0.
  rewrite /f (@hOff (set_val x) (set_valP x) hx).
  exact: (real_seminorm_zero hN.1).
have hSupport : @real_function_support R UT (fun x => N (f x)) `<=` C.
  exact: (real_function_support_in_closed_set hClosed hNormOff).
have hCompact : compact (@real_function_support R UT (fun x => N (f x))).
  exact: (@subclosed_compact UT
    (@real_function_support R UT (fun x => N (f x))) C
    (@real_function_support_closed R UT (fun x => N (f x))) hC hSupport).
have hField : compact_continuous_vector_fields hN f := conj hF hCompact.
split.
- exact: (@compact_continuous_vector_normed_measurable R UT Y N hN
    (@current_form_separable R h2 n d) (@euclidean_open_domain_measure R n U)
    (proj1 (@euclidean_open_domain_measure_laws R n U hU))
    (proj2 (@euclidean_open_domain_measure_laws R n U hU)) f hField).
- have [a [hA hCap]] := @norm_class_zero_compact_bounded R X Y NX N hNX hN
    U (smooth_compact_carrier K) phi (smooth_compact_is_compact K)
    (smooth_compact_in_domain K) hPhi.
  exists a; split; first exact: ltW hA.
  move=> x; have [hx|hx] := pselect (smooth_compact_carrier K (set_val x)).
  + exact: (@hCap (set_val x) hx).
  + rewrite (@hOff (set_val x) (set_valP x) hx).
    change (is_true (N (0:Y)<=a)).
    have hZero : N (0:Y)=0 := real_seminorm_zero hN.1.
    by rewrite hZero; exact: ltW hA.
Qed.
