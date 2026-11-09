(** Federer (1969), 3.4.5, p. 321: finite actual
    remainder coefficients vanish by analytic uniqueness at
    the actual flat endpoint. This is the internal real
    proof of the adapted example cited to Cartan (1957). *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets boolp ring.
From Federer Require Import RealNormUP NormDifferentialUP HilbertFormCompactness NormAnalyticUP
  NormAnalyticDomain NormAnalyticOperations NormAnalyticScalarProducts NormOpenDomainLaws ScalarAffineAnalytic
  FlatExponentialSealed CartanCoefficientAnalytic QuadraticSubstitutionParameterCoefficients
  ClearedQuadraticSubstitution AnalyticQuadraticCoefficientOperators FlatPolynomialAnalyticIndependence
  ScalarAnalyticGlobalUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Independence.
Variable R:realType.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation AN f:=(@norm_analytic R R^o R^o N N hN hN setT f).

(** Source for [cleared_flat_parameter_coefficients_zero]: every
    finite original analytic parameter coefficient is zero
    everywhere if its actual cleared flat polynomial is zero
    below the endpoint, supporting 3.4.5, p. 321.
    Analyticity is proved for the actual finite operators;
    no independence or analytic continuation is assumed. *)
Theorem cleared_flat_parameter_coefficients_zero parity order (f:nat->nat->R->R):
  (forall i k,AN (f i k)) ->
  (forall z,z<1 ->quadratic_cleared_remainder parity order z (FlatExponential.value (1-z))
    (fun i k=>f i k z)=0) ->
  forall ell z,quadratic_substitution_parameter_coefficient parity order ell (fun i k=>f i k z)=0.
Proof.
move=>hf hRelation ell z.
case:(leqP ell order)=>[hEll|hBeyond].
- pose A:=fun ell z=>quadratic_substitution_parameter_coefficient parity order ell (fun i k=>f i k z).
  have hA j:AN (A j):=@quadratic_parameter_coefficient_analytic R R^o N hN setT
    (fun x _=>norm_full_domain_interior N x) parity order j f hf.
  have hId:AN (fun z=>z).
    move=>t _;have hh:=@scalar_affine_analytic_at R 1 0 t.
    apply:(norm_analytic_at_domain_agreement _ hh)=>y _;by rewrite mul1r addr0.
  pose W:=fun j z=>z^+(order-j)*A j z.
  have hW j:AN (W j):=norm_analytic_scalar_product (norm_analytic_scalar_power (order-j)%N hId) (hA j).
  pose g:=fun j t=>W j (1-t).
  have hg j:AN (g j):=norm_analytic_compose_on (fun t (_:setT t)=>Logic.I)
    (@cartan_coefficient_shift_analytic R) (hW j).
  have hFlat t (ht:0<t<1):(\sum_(j<order.+1) g j t*(FlatExponential.value t)^+j)=0.
    have hTwice:1-(1-t)=t by ring.
    have hPositive:0<1-(1-t) by rewrite hTwice;exact:(andP ht).1.
    have hLower:1-t<1 by move:hPositive;rewrite subr_gt0.
    have hh:=hRelation (1-t) hLower.
    rewrite /quadratic_cleared_remainder hTwice in hh.
    have hSum:(\sum_(j<order.+1) g j t*(FlatExponential.value t)^+j)=
      \sum_(j<order.+1) (1-t)^+(order-j)*(FlatExponential.value t)^+j*A j (1-t).
      apply:eq_bigr=>j _;rewrite /g /W;ring.
    by rewrite hSum.
  have [d [hd hZero]]:=@flat_polynomial_analytic_coefficients_vanish R order.+1 g 1
    (fun j _=>hg j 0 Logic.I) (ltr01) hFlat ell (hEll).
  have hGlobal t:g ell t=0.
    apply:(scalar_global_analytic_right_zero (hg ell) hd)=>u /andP[hu0 hu].
    apply:hZero;by rewrite ger0_norm ?(ltW hu0).
  have hWZero t:W ell t=0.
    have hh:=hGlobal (1-t);rewrite /g in hh.
    have hTwice:1-(1-t)=t by ring.
    by rewrite hTwice in hh.
  apply:(scalar_global_analytic_right_zero (hA ell) (ltr01))=>t /andP[ht0 ht1].
  have hh:=hWZero t;rewrite /W in hh.
  have htNonzero:t!=0 by rewrite (gt_eqF ht0).
  have hPower:t^+(order-ell)!=0 by apply:expf_neq0.
  by move/eqP:hh;rewrite mulf_eq0 (negbTE hPower) /= =>/eqP.
- rewrite /quadratic_substitution_parameter_coefficient;apply:big1=>i _;apply:big1=>k /andP[hk /eqP hEqual].
  have hLe:(ell<=i+2*k+parity+ell)%N:=leq_addl _ ell.
  rewrite hEqual in hLe;have hh:=leq_ltn_trans hLe hBeyond;by rewrite ltnn in hh.
Qed.
End Independence.
