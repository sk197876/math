(** Federer (1969), 3.2.33, p. 270: coordinate
    derivatives and the original relative differential have
    exactly the same image dimension, by 3.1.22(3), p. 235. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations PartialFunctionUP PartialFunctionBasic
  PartialMetricLipschitz ParametricDifferentialUP PartialImageDimensionUP PartialTotalLinearImageDimension LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [parametric_partial_image_range]: the image
    of Df relative to W equals the image of D(f composed
    with psi), supporting S in Federer 3.2.33, p. 270,
    by the exact graph criterion of 3.1.22(3), p. 235.
    The statement does not require a globally selected chart
    or derivative, and supplies no outside-tangent values. *)
Lemma parametric_partial_image_range (R:fieldType) (X Z Y:lmodType R)
    (J:Hom Z X) (Q:Hom Z Y) (d:partial_function X Y):
  is_parametric_differential_restriction J Q d ->
  partial_function_range d=partial_function_range (partial_function_total Q).
Proof.
move=>hParam; apply/seteqP; split=>y.
- move=>[v hv]; have [w [_ hw]]:=(hParam v y).1 hv.
  exists w; exact hw.
- move=>[w hw]; exists (J w); apply:(hParam (J w) y).2.
  exists w; by split.
Qed.

(** Source for [parametric_partial_low_image_iff]: the
    original image-dimension condition in 3.2.32 is unchanged
    in analytic coordinates, Federer 3.2.33, p. 270.
    The independent exact range law and the actual rank of
    Q prove both directions, for every natural dimension. *)
Lemma parametric_partial_low_image_iff (R:realType) n m v mu
    (J:Hom (R_n R m) (R_n R n)) (Q:Hom (R_n R m) (R_n R v))
    (d:partial_function (R_n R n) (R_n R v)):
  is_parametric_differential_restriction J Q d ->
  (is_partial_image_dimension_at_most mu d <->
    exists r,has_linear_rank Q r /\(r<=mu)%N).
Proof.
move=>hParam.
have hRange:=parametric_partial_image_range hParam.
have hSame:is_partial_image_dimension_at_most mu d <->
    is_partial_image_dimension_at_most mu (partial_function_total Q).
  by rewrite /is_partial_image_dimension_at_most hRange.
exact:(iff_trans hSame (partial_total_linear_low_image_iff mu Q)).
Qed.
