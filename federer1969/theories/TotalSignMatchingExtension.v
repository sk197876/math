(** Federer (1969), 2.5.7, p. 98, uses the sign-matching dual tests of
    2.4.16, pp. 89–90, to bound candidate densities. The erratum p. 2, book
    p. 98 line 10, requires total-domain functions. This supporting adapter
    proves that equality of partial sign graphs with a total function forces
    a total domain, and then uses the sealed extension interface without
    changing any graph value. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed ScalarSignTest MeasureDualTestUP TotalSignMatching.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sign_matching_total_domain]: supporting domain consequence
    of sign(u)=sign(f) in Federer 2.4.16, p. 89, used in 2.5.7, p. 98. The
    equality includes the domains of the partial sign functions *)
Lemma sign_matching_total_domain (R : realType) (X : Type)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_sign_matching_test (partial_function_total f) u ->
  forall x, partial_function_domain u x.
Proof.
move=> hs x.
have hf : partial_function_graph (partial_scalar_sign (partial_function_total f)) x (Num.sg (f x)).
  exists (f x); by split.
have [y [hy _]] := (hs x _).1 hf; by exists y.
Qed.

(** Source for [sign_matching_total_extension_graph]: supporting
    identification of a dual test with its sealed total extension for
    Federer 2.5.7, p. 98, using 2.4.16, p. 89.
    This is exact graph equality, stronger than merely almost equality;
    no values are changed because the original test is already total. *)
Lemma sign_matching_total_extension_graph (R : realType) (X : Type)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_sign_matching_test (partial_function_total f) u ->
  forall x y, partial_function_graph u x y <->
    partial_function_graph (partial_function_total (PartialFunctionExtension.value u 0)) x y.
Proof.
move=> hs x y; split.
- exact: (@PartialFunctionExtension.laws X _ u 0 x y).
- move=> he.
  have [z hz] := @sign_matching_total_domain R X f u hs x.
  have hz' := @PartialFunctionExtension.laws X _ u 0 x z hz.
  have he' : PartialFunctionExtension.value u 0 x=y := he.
  by rewrite -he' hz'.
Qed.

(** Source for [sign_matching_extension_pointwise]: the pointwise sign
    condition on total dual tests used in Federer 2.5.7, pp. 98–99 *)
Lemma sign_matching_extension_pointwise (R : realType) (X : Type)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_sign_matching_test (partial_function_total f) u ->
  forall x, Num.sg (PartialFunctionExtension.value u 0 x)=Num.sg (f x).
Proof.
move=> hs x.
have hf : partial_function_graph (partial_scalar_sign (partial_function_total f)) x (Num.sg (f x)).
  exists (f x); by split.
have [y [hy he]] := (hs x _).1 hf.
by rewrite (@PartialFunctionExtension.laws X _ u 0 x y hy).
Qed.

(** Source for [sign_matching_extension_nonnegative]: positivity of the
    sign-matching tests used to bound the candidate density in Federer
    2.5.7, p. 98 This is a consequence of sign equality, not an extra
    restriction on the tests of 2.4.16. *)
Lemma sign_matching_extension_nonnegative (R : realType) (X : Type)
    (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))
    (u : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_sign_matching_test (partial_function_total f) u ->
  (forall x, 0 <= f x) -> forall x, 0 <= PartialFunctionExtension.value u 0 x.
Proof.
move=> hs hf x; rewrite -sgr_ge0 (@sign_matching_extension_pointwise R X f u hs x) sgr_ge0.
exact: hf x.
Qed.
