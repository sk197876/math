(** Federer (1969), 4.1.9, p. 364: the exact
    affine power moment in the middle mass estimate.
    Reuse the original scalar differential calculus and
    interval fundamental theorem, and MathComp's finite
    geometric-sum identity. The diagonal and degree zero
    are included; no division by a possibly zero slope remains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP NormOpenDomainLaws
  NormDifferentialArithmetic NormClassOneUP NormClassOneLaws NormClassZeroArithmetic ScalarAffineDifferentials ScalarPowerDifferential
  ScalarCoefficientLinearAlgebra RealClassOneSegmentIntegral RealSubsetIntegralAgreement
  LebesgueScalarMeasure RealMetricBackground MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarAffinePowerMoment.
Variable R:realType.
Variables a b:R.
Variable j:nat.
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation full := (fun _:R=>True).
Local Notation hFull := (fun (t:R) (_:True)=>@norm_full_domain_interior R R^o NS t).
Local Notation affine := (fun t:R=>(b-a)*t+a).
Local Notation G := (fun t:R=>affine t^+j).
Local Notation mean := ((\sum_(k<j.+1) a^+k*b^+(j-k))/j.+1%:R).

(** Source for [scalar_affine_power_difference]: the finite
    geometric sum underlying the exact middle coefficient
    in Federer 4.1.9, p. 364. This is a direct
    application of the existing commutative-ring identity. *)
Lemma scalar_affine_power_difference:
  b^+j.+1-a^+j.+1=(b-a)*(\sum_(k<j.+1) a^+k*b^+(j-k)).
Proof.
rewrite subrXX;congr ((b-a)*_);apply:eq_bigr=>k _.
exact:mulrC.
Qed.

(** Source for [scalar_affine_power_differential]: the actual
    scalar affine-power differential used for the original
    time integral in Federer 4.1.9, p. 364. *)
Lemma scalar_affine_power_differential m t:
  has_norm_differential NS NS full (fun s=>affine s^+m) t
    (@scalar_coefficient_linear_map R R^o (m%:R*affine t^+m.-1*(b-a))).
Proof.
have hAffine:=@scalar_affine_derivative_step R (b-a) a full hFull 0%N t I.
exact:(@norm_curve_power_differential R full affine t (b-a) m hAffine).
Qed.

(** Source for [scalar_affine_power_class_zero]: the original
    affine power integrand is continuous, supporting its
    ordinary interval integral in Federer 4.1.9, p. 364. *)
Lemma scalar_affine_power_class_zero:norm_class_zero NS NS full G.
Proof.
exact:(@norm_everywhere_differentiable_class_zero R R^o R^o NS NS hNS full G
  (fun t=>@scalar_coefficient_linear_map R R^o (j%:R*affine t^+j.-1*(b-a)))
  (fun t _=>scalar_affine_power_differential j t)).
Qed.

(** Source for [scalar_affine_power_moment_off_diagonal]: the
    original affine power moment when the endpoint values
    differ, supporting Federer 4.1.9, p. 364. The
    exact slope cancellation uses its explicit nonzero proof. *)
Lemma scalar_affine_power_moment_off_diagonal:b!=a->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand G) mean%:E.
Proof.
move=>hDifferent.
have hSlope:(b-a)!=0 by rewrite subr_eq0.
have hNat:(j.+1%:R:R)!=0 by rewrite pnatr_eq0.
pose c:=(j.+1%:R:R)^-1*(b-a)^-1.
pose F t:=c*affine t^+j.+1.
have hCoefficient t:c*(j.+1%:R*affine t^+j*(b-a))=G t.
  have hReorder:c*(j.+1%:R*affine t^+j*(b-a))=(c*(b-a)*j.+1%:R)*affine t^+j by ring.
  rewrite hReorder /c -[(_^-1*(b-a)^-1)*(b-a)]mulrA mulVf // mulr1 mulVf // mul1r.
  by [].
have hDerivative t:has_norm_differential NS NS full F t
    (@scalar_coefficient_linear_map R R^o (G t)).
  have hScaled:=@norm_differential_scale R R^o R^o NS NS hNS hNS full
    (fun s=>affine s^+j.+1) t _ c (scalar_affine_power_differential j.+1 t).
  rewrite -scalar_coefficient_linear_scale in hScaled.
  change (has_norm_differential NS NS full F t
    (@scalar_coefficient_linear_map R R^o (c*(j.+1%:R*affine t^+j*(b-a))))) in hScaled.
  by rewrite hCoefficient in hScaled.
have hIntegral:=@real_class_one_segment_integral R F G 0 1 ler01 hDerivative scalar_affine_power_class_zero.
have hEndpoints:F 1-F 0=mean.
  rewrite /F mulr1 subrK mulr0 add0r -mulrBr scalar_affine_power_difference /c
    mulrA -[(_^-1*(b-a)^-1)*(b-a)]mulrA mulVf // mulr1.
  exact:mulrC.
by rewrite hEndpoints in hIntegral.
Qed.

(** Source for [scalar_affine_power_moment_diagonal]: equal
    endpoint derivative norms cause no exceptional case in
    the original coefficient, Federer 4.1.9, p. 364.
    Its printed mean is exactly the constant a^j. *)
Lemma scalar_affine_power_moment_diagonal:b=a->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand G) mean%:E.
Proof.
move=>hEqual.
have hMean:mean=a^+j.
  have hSum:(\sum_(k<j.+1) a^+k*b^+(j-k))=(a^+j)*j.+1%:R.
    rewrite hEqual.
    transitivity (\sum_(k<j.+1) a^+j).
    - apply:eq_bigr=>k _.
      have hk:(k<=j)%N by move:(ltn_ord k);rewrite ltnS.
      by rewrite -exprD (subnKC hk).
    - by rewrite sumr_const card_ord mulr_natr.
  have hNat:(j.+1%:R:R)!=0 by rewrite pnatr_eq0.
  by rewrite hSum (mulfK hNat).
pose F t:=a^+j*t.
have hDerivative t:has_norm_differential NS NS full F t
    (@scalar_coefficient_linear_map R R^o (a^+j)).
  have hAffine:=@scalar_affine_derivative_step R (a^+j) 0 full hFull 0%N t I.
  change (has_norm_differential NS NS full (fun s=>a^+j*s+0) t
    (@scalar_coefficient_linear_map R R^o (a^+j))) in hAffine.
  have hFunction:(fun s:R=>a^+j*s+0)=F by apply:funext=>s;rewrite addr0.
  by rewrite hFunction in hAffine.
have hContinuous:=@norm_class_zero_constant R R^o R^o NS NS hNS full (a^+j) hFull.
have hIntegral:=@real_class_one_segment_integral R F (fun _=>a^+j) 0 1 ler01 hDerivative hContinuous.
rewrite /F mulr1 mulr0 subr0 in hIntegral.
have hOriginal:is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun _=>a^+j)) mean%:E.
  rewrite hMean;exact:hIntegral.
apply:(@real_subset_integral_agreement R (real_line_metric R) (@lebesgue_scalar_measure R)
  (`[0,1]:set R) (fun _=>a^+j) G mean%:E _ hOriginal)=>t ht.
by rewrite /G hEqual subrr mul0r add0r.
Qed.

(** Source for [scalar_affine_power_moment]: the exact
    original time mean of ((1-t)a+tb)^j is the sum
    of a^k b^(j-k) divided by j+1, Federer 4.1.9,
    p. 364. Both zero endpoints, coincident endpoints
    and degree zero are retained. *)
Theorem scalar_affine_power_moment:
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun t=>((1-t)*a+t*b)^+j)) mean%:E.
Proof.
have hIntegral:is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand G) mean%:E.
  case:(pselect (b=a))=>hEqual.
  - exact:scalar_affine_power_moment_diagonal hEqual.
  - exact:scalar_affine_power_moment_off_diagonal (introN eqP hEqual).
apply:(@real_subset_integral_agreement R (real_line_metric R) (@lebesgue_scalar_measure R)
  (`[0,1]:set R) G (fun t=>((1-t)*a+t*b)^+j) mean%:E _ hIntegral)=>t ht.
congr (_^+j);ring.
Qed.
End ScalarAffinePowerMoment.
