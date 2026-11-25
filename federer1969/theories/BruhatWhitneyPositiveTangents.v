(** Federer (1969), 3.4.10, p. 338:
    obtain the actual signed curve tangents and
    the axis tangent on the cited original surface.
    Apply the already proved differential-image inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialLocal NormOpenDomainLaws NormHigherCurveDerivativeUP NormedPrimitiveCell
  TangentConeUP AnalyticCurveTangentVector GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness BruhatWhitneyPositiveCurves
  BruhatWhitneyPositiveCurveDifferential BruhatWhitneyAxis BruhatWhitneySurfaceUP
  BruhatWhitneySurfaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_positive_curve_base_axis]: the
    checked coordinate formula identifies the original curve's
    base with the actual axis, 3.4.10, p. 338. *)
Lemma bruhat_whitney_positive_curve_base_axis (R:realType) (b s:R):
  @bruhat_whitney_positive_curve R b s 0=@bruhat_whitney_axis R b.
Proof.
apply/ffunP=>i.
case h0:(i==ord0).
- move/eqP:h0=>->;rewrite (bruhat_whitney_positive_curve_base b s).1
    (bruhat_whitney_axis_coordinates b).1;done.
case h1:(i==Ordinal (isT:(1<3)%N)).
- move/eqP:h1=>->;rewrite (bruhat_whitney_positive_curve_base b s).2.1
    (bruhat_whitney_axis_coordinates b).2.1;done.
have hi:i=ord_max.
  apply:val_inj;case:i h0 h1=>[i hi] /= h0 h1.
  by case:i hi h0 h1=>[|[|[|i]]].
by rewrite hi (bruhat_whitney_positive_curve_base b s).2.2
  (bruhat_whitney_axis_coordinates b).2.2.
Qed.

(** Source for [bruhat_whitney_signed_curve_tangent]: the
    genuine curve through the original axis point supplies
    direction (s,1,b), supporting 3.4.10, p. 338. *)
Theorem bruhat_whitney_signed_curve_tangent (R:realType) (b s:R):
  s^+2=b ->norm_tangent_cone (inner_norm (@euclidean_inner_productP R 3))
    (@BruhatWhitneySurface.set R) (@bruhat_whitney_axis R b)
    [ffun i=>if i==ord0 then s else if i==Ordinal (isT:(1<3)%N) then 1 else b].
Proof.
move=>hS.
have [L [hD hL]]:=@bruhat_whitney_positive_curve_differential R b s.
have hMember t (ht:0<1+4*t):
    @BruhatWhitneySurface.set R (@bruhat_whitney_positive_curve R b s t).
  exact:bruhat_whitney_positive_curve_membership hS (ltW ht).
have hTan:=@differentiable_curve_tangent_vector R (R_n R 3)
  (inner_norm (@euclidean_inner_productP R 3))
  (inner_norm_real_norm (@euclidean_inner_productP R 3))
  [set t|0<1+4*t] (@BruhatWhitneySurface.set R)
  (@bruhat_whitney_positive_curve R b s) 0 L hD hMember.
by rewrite bruhat_whitney_positive_curve_base_axis hL scale1r in hTan.
Qed.

(** Source for [bruhat_whitney_axis_tangent]: the actual
    complete axis is on the original surface, so
    its coordinate direction is tangent at every axis
    point, supporting 3.4.10, p. 338. *)
Theorem bruhat_whitney_axis_tangent (R:realType) (b:R):
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R 3))
    (@BruhatWhitneySurface.set R) (@bruhat_whitney_axis R b)
    (@coordinate_basis R 3 ord_max).
Proof.
pose X:=R_n R 3.
pose NX:=inner_norm (@euclidean_inner_productP R 3).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3).
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose e:=@coordinate_basis R 3 ord_max.
pose L:=@scalar_coefficient_linear_map R X e.
have hLinear:=@norm_differential_linear R R^o X N NX hN hNX setT 0 L
  (norm_full_domain_interior N 0) (scalar_coefficient_linear_bound hNX e).
have hConstant:=@norm_differential_constant R R^o X N NX hN hNX setT 0
  (@bruhat_whitney_axis R b) (norm_full_domain_interior N 0).
have hSum:=norm_differential_add hNX hLinear hConstant.
rewrite addr0 in hSum.
have hMember t:setT t ->@BruhatWhitneySurface.set R (L t+@bruhat_whitney_axis R b).
  move=>_.
  change (@BruhatWhitneySurface.set R (t*:e+b*:e)).
  rewrite -scalerDl;exact:bruhat_whitney_axis_membership.
have hTan:=@differentiable_curve_tangent_vector R X NX hNX setT
  (@BruhatWhitneySurface.set R) (fun t=>L t+@bruhat_whitney_axis R b) 0 L hSum hMember.
rewrite linear0 add0r in hTan.
change (norm_tangent_cone NX (@BruhatWhitneySurface.set R)
  (@bruhat_whitney_axis R b) (1*:e)) in hTan.
by rewrite scale1r in hTan.
Qed.
