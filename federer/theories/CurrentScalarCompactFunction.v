(** Federer (1969), 4.1.1, pp. 344–345,
    and 4.1.7, p. 356, used in
    4.1.12, pp. 368–369: every actual
    smooth compact scalar function is an original
    zero-form test, with the same pointwise values
    and compact support. Reuse the existing scalar
    test realization and zero-form coefficient maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentCoefficientNorms
  CurrentSpaces CurrentSupportGeometry CurrentScalarTestMaps CurrentZeroCovectorMaps Distributions SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScalarCompactFunction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hAbs := (@scalar_absolute_value_norm R).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU 0%N).
Local Notation ev := (@current_smooth_value R h2 n U hU 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation F := (@distribution_smooth_space R X R^o NX (fun t:R^o=>`|t|) hNX hAbs U hU).
Local Notation fv := (@distribution_smooth_value R X R^o NX (fun t:R^o=>`|t|) hNX hAbs U hU).
Local Notation hF := (@distribution_smooth_laws R X R^o NX (fun t:R^o=>`|t|) hNX hAbs U hU).

(** Source for [current_scalar_compact_function_exists]:
    an independently given smooth scalar function vanishing
    off K has an actual original zero-form test
    with exactly those values and support in K,
    supporting the examples of Federer 4.1.12,
    pp. 368–369, by the already proved compact
    test realization and A^0=R. *)
Theorem current_scalar_compact_function_exists (K:smooth_compact_set hNX U) (f:X->R^o):
  norm_class_all_orders hNX hAbs U f->
  (forall x,~smooth_compact_carrier K x->f x=0)->
  exists gamma:@current_test_space R h2 n U hU 0%N,
    (forall x,U x->@current_test_value R h2 n U hU 0%N gamma x=@zero_form R X R^o (f x)) /\
    @CurrentSupportGeometry.current_test_support R h2 n 0%N U hU gamma `<=` smooth_compact_carrier K.
Proof.
move=>hSmooth hOff.
have[psi hPsi]:=@smooth_test_represents_compact_function R X R^o NX (fun t:R^o=>`|t|)
  hNX hAbs U F fv hF K f hSmooth hOff.
pose gamma:=@current_zero_form_test R h2 n U hU psi.
have hValue x (hx:U x):@current_test_value R h2 n U hU 0%N gamma x=@zero_form R X R^o (f x).
  change (smooth_test_value hE (@current_zero_form_test R h2 n U hU psi) x=
    @zero_form R X R^o (f x)).
  rewrite (@current_zero_form_test_values R h2 n U hU psi x hx).
  change (@zero_form R X R^o (smooth_test_value hF psi x)=@zero_form R X R^o (f x)).
  by rewrite (hPsi x hx).
exists gamma;split;first exact:hValue.
apply:(@smooth_function_compact_support_iff R X (A_m X R^o 0%N) NX
  (@current_form_comass R h2 n 0%N) hNX (@current_form_comass_real_norm R h2 n 0%N)
  U E ev hE K (smooth_test_inclusion hE gamma)).2=>x hxOff.
case:(pselect (U x))=>hx.
- change (@current_test_value R h2 n U hU 0%N gamma x=0).
  by rewrite (hValue x hx) (hOff x hxOff) linear0.
- exact:(smooth_function_evaluation_outside hE _ hx).
Qed.
End CurrentScalarCompactFunction.
