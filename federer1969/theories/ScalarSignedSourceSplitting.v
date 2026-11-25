(** Federer (1969), 3.2.6, p. 246: the final
    source calculation subtracts the norm-weighted negative
    derivative piece from the positive derivative piece.
    Actual derivatives and both omitted endpoints are handled
    by an explicit conull comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology RealCurveDerivativeUP RealCurveDerivativeIntegrands
  RealDerivativeRepresentative LocallyAbsolutelyContinuousCurve ScalarCurveDerivativeLoci ScalarDerivativeSignMembership
  ScalarAbsoluteContinuousArea WeightedRealDerivativeIntegrand PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct PartialExtendedArithmetic PartialSimpleIntegralError
  MeasureUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_signed_substitution_source]: the
    source integrand (g composed with f) f' on [a,b]
    in the second equation of Federer 3.2.6, p. 245.
    The actual scalar derivative remains partial. *)
Definition scalar_signed_substitution_source (R:realType) (f g:R->R) a b:=
  partial_function_zero_extension (0:extended_real_line R) (`[a,b]:set (real_line_metric R))
    (weighted_real_curve_derivative_integrand (g \o f) f).

(** Source for [scalar_area_source_actual_value]: supporting
    actual weighted speed on one of A_1,A_2 in
    Federer 3.2.6, p. 246. No measurability of
    the real weight is needed for a graph value. *)
Lemma scalar_area_source_actual_value (R:realType) (f g:R->R) (A:set (real_line_metric R)) x v:
  has_real_curve_derivative f x v -> A x ->
  partial_function_graph (scalar_curve_area_source_integrand f A g) x (g (f x) * `|v|)%:E.
Proof.
move=>hv hx; apply/partial_function_zero_extension_graph; left; split=>//.
apply/partial_density_product_graph; exists (g (f x))%:E,`|v|%:E; split=>//; split.
- by exists v; split.
- by rewrite -EFinM.
Qed.

(** Source for [scalar_area_source_off]: supporting zero
    outside a selected sign piece in the calculation of
    Federer 3.2.6, p. 246. *)
Lemma scalar_area_source_off (R:realType) (f g:R->R) (A:set (real_line_metric R)) x:
  ~A x -> partial_function_graph (scalar_curve_area_source_integrand f A g) x 0.
Proof. move=>hx; apply/partial_function_zero_extension_graph; right; by split. Qed.

(** Source for [scalar_signed_source_sign_split]: the
    final source subtraction in Federer 3.2.6, p. 246.
    Undefined derivatives and the two endpoints are excluded
    only in this almost-equality statement. *)
Theorem scalar_signed_source_sign_split (R:realType) (f g:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) ->
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_extended_function_subtract
      (scalar_curve_area_source_integrand f (scalar_positive_derivative_set f a b) g)
      (scalar_curve_area_source_integrand f (scalar_negative_derivative_set f a b) g))
    (scalar_signed_substitution_source f g a b).
Proof.
move=>hAC; have hm:=lebesgue_scalar_is_measure R.
pose P:=scalar_positive_derivative_set f a b.
pose N:=scalar_negative_derivative_set f a b.
pose U:=scalar_curve_area_source_integrand f P g.
pose V:=scalar_curve_area_source_integrand f N g.
have hSub:=scalar_derivative_sign_sets_subinterval f a b.
have hD:=bv_real_derivative_representative_ae (locally_absolutely_continuous_curve_finite_variation hAC).
pose E:=[set a] `|` [set b].
have hE:lebesgue_scalar_measure E=0%E.
  exact (measure_null_union hm (lebesgue_scalar_singleton a) (lebesgue_scalar_singleton b)).
have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R) (~` E).
  by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_and hm hD hOff))=>x [hDx hxE].
pose v:=real_derivative_representative f x.
case:(pselect ((`[a,b]:set (real_line_metric R)) x))=>hx.
- move:(hx); rewrite /= in_itv /= =>/andP[hax hxb].
  have hxa:x!=a by apply/eqP=>he; apply:hxE; left; exact he.
  have hxb0:x!=b by apply/eqP=>he; apply:hxE; right; exact he.
  have hax':a<x by rewrite lt_neqAle eq_sym hxa hax.
  have hxb':x<b by rewrite lt_neqAle hxb0 hxb.
  have hSigns:=scalar_sign_interval_sets_at hax' hxb' hDx.
  have hS:partial_function_graph (scalar_signed_substitution_source f g a b) x (g (f x)*v)%:E.
    apply/partial_function_zero_extension_graph; left; split=>//.
    apply/weighted_real_derivative_integrand_graph; exists v; by split.
  exists (g (f x)*v)%:E; split; last exact hS.
  case:(ltP 0 v)=>hPos.
  + have hP:P x:=(hSigns.1).2 hPos.
    have hNotN:~N x.
      move=>hN; have hNeg:=(hSigns.2).1 hN.
      by have:=lt_trans hPos hNeg; rewrite ltxx.
    have hU:=scalar_area_source_actual_value g hDx hP.
    rewrite (ger0_norm (ltW hPos)) in hU.
    have hV:=@scalar_area_source_off R f g N x hNotN.
    have hDiff:=@partial_subtract_finite_graph R [the choiceType of real_line_metric R] U V x (g (f x)*v) 0 hU hV.
    by rewrite subr0 in hDiff.
  + case:(eqVneq v 0)=>[hv0|hv0].
    * have hNotP:~P x.
        move=>hP; have hh:0<v:=(hSigns.1).1 hP; by rewrite hv0 ltxx in hh.
      have hNotN:~N x.
        move=>hN; have hh:v<0:=(hSigns.2).1 hN; by rewrite hv0 ltxx in hh.
      have hU:=@scalar_area_source_off R f g P x hNotP.
      have hV:=@scalar_area_source_off R f g N x hNotN.
      have hDiff:=@partial_subtract_finite_graph R [the choiceType of real_line_metric R] U V x 0 0 hU hV.
      have hVal:g (f x)*v=0 by rewrite hv0 mulr0.
      rewrite hVal; by rewrite subrr in hDiff.
    * have hNeg:v<0 by rewrite lt_neqAle hv0 hPos.
      have hN:N x:=(hSigns.2).2 hNeg.
      have hNotP:~P x.
        move=>hP; have hp:=(hSigns.1).1 hP.
        by have:=lt_trans hp hNeg; rewrite ltxx.
      have hU:=@scalar_area_source_off R f g P x hNotP.
      have hV:=scalar_area_source_actual_value g hDx hN.
      rewrite (ler0_norm (ltW hNeg)) in hV.
      have hDiff:=@partial_subtract_finite_graph R [the choiceType of real_line_metric R] U V x 0 (g (f x)*(-v)) hU hV.
      by rewrite sub0r mulrN opprK in hDiff.
- have hNotP:~P x by move=>hP; exact (hx (hSub.1 x hP)).
  have hNotN:~N x by move=>hN; exact (hx (hSub.2 x hN)).
  have hU:=@scalar_area_source_off R f g P x hNotP.
  have hV:=@scalar_area_source_off R f g N x hNotN.
  have hDiff:=@partial_subtract_finite_graph R [the choiceType of real_line_metric R] U V x 0 0 hU hV.
  exists 0; split; first by rewrite subrr in hDiff.
  apply/partial_function_zero_extension_graph; right; by split.
Qed.
