(** Federer (1969), 3.4.5, p. 321: actual global
    analytic functions vanishing on the cited local analytic
    example have zero finite cleared remainders. The adapted
    real proof uses actual finite jets and 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearSealed NormAnalyticUP NormAnalyticDomain NormAnalyticOperations
  NormAnalyticScalarProducts FlatExponentialSealed CartanSurfaceUP CartanSurfaceSealed CartanSurfaceEquation
  CartanCoordinateGeometry CartanLowerAxisAnalytic CartanRationalArcAnalytic CartanFiniteJetDivision
  NormFiniteJetAgreement NormFiniteJetAgreementOperations AnalyticDirectionalCoefficient
  AnalyticIteratedDirectionalCoefficients CartanAxisCoefficientTransport
  CartanMultipleClearedRemainder AnalyticQuadraticCoefficientOperators QuadraticCoefficientJetAgreement
  ClearedQuadraticSubstitution ScalarAnalyticFlatComparisons.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Remainders.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X R^o NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN).
Local Notation NZ:=(fun i=>@ContinuousMultilinear.norm R i X R^o NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X R^o NX N hNX hN).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation J:=([set z:R^o|z<1]).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation AN A f:=(@norm_analytic R X R^o NX N hNX hN A f).
Local Notation ScalarAN A f:=(@norm_analytic R R^o R^o N N hN hN A f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [cartan_axis_cleared_remainders_zero]: for
    every original finite remainder order and both original
    parities, an actual global analytic function zero on
    the actual surface has identically zero lower-axis remainder,
    supporting 3.4.5, p. 321. Every finite jet
    comparison uses a proved actual analytic quotient witness. *)
Theorem cartan_axis_cleared_remainders_zero (f:X->R) (C:nat->X->R) (P:nat->nat->X->R)
    parity order:
  AN setT f ->(forall v,CartanSurface.set v ->f v=0) ->
  (forall i,Coefficient setT f i (@coordinate_basis R 3 ord0) (C i) /\AN setT (C i)) ->
  (forall i k,Coefficient setT (C i) k (@coordinate_basis R 3 j) (P i k) /\AN setT (P i k)) ->
  (parity=0%N \/parity= 1%N) ->
  forall z,z<1 ->quadratic_cleared_remainder parity order z (FlatExponential.value (1-z))
    (fun i k=>P i (2*k+parity)%N (cartan_axis_point z))=0.
Proof.
move=>hf hZero hC hP hParity.
have hU0:U 0 by rewrite /= ffunE;exact:ltr01.
have hJ0:J 0:=ltr01.
have hPU i k:AN U (P i k):=norm_analytic_open_restriction
  (fun v (_:U v)=>Logic.I) (@cartan_lower_domain_interior R) (hP i k).2.
have hB i k:ScalarAN J (fun z=>P i k (cartan_axis_point z)):=
  cartan_lower_axis_restriction_analytic (hPU i k).
pose F:=fun z:R=>quadratic_cleared_remainder parity order z (FlatExponential.value (1-z))
  (fun i k=>P i (2*k+parity)%N (cartan_axis_point z)).
have hF:ScalarAN J F:=@quadratic_cleared_remainder_analytic R R^o N hN J
  (@cartan_arc_domain_interior R) parity order (fun z=>z) (fun z=>FlatExponential.value (1-z))
  (fun i k z=>P i (2*k+parity)%N (cartan_axis_point z))
  (@cartan_lower_axis_identity_analytic R) (@cartan_lower_axis_coefficient_analytic R)
  (fun i k=>hB i (2*k+parity)%N).
apply:(scalar_analytic_finite_flat_comparison hF)=>m.
pose L:=(3*order+parity+m)%N.
have [q [hq hAgree]]:=@cartan_surface_finite_jet_division R f L hf hZero.
pose g:=fun v:X=>q v*cartan_surface_equation v.
have hg:AN U g:=norm_analytic_scalar_product hq (@cartan_surface_original_equation_analytic R).
have [D [B [hD hBq]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  U q (@coordinate_basis R 3 ord0) (@coordinate_basis R 3 j) hq.
have [E [H [hE hH]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  U g (@coordinate_basis R 3 ord0) (@coordinate_basis R 3 j) hg.
have hAxisH i k:ScalarAN J (fun z=>H i k (cartan_axis_point z)):=
  cartan_lower_axis_restriction_analytic (hH i k).2.
pose G:=fun z:R=>quadratic_cleared_remainder parity order z (FlatExponential.value (1-z))
  (fun i k=>H i (2*k+parity)%N (cartan_axis_point z)).
have hG:ScalarAN J G:=@quadratic_cleared_remainder_analytic R R^o N hN J
  (@cartan_arc_domain_interior R) parity order (fun z=>z) (fun z=>FlatExponential.value (1-z))
  (fun i k z=>H i (2*k+parity)%N (cartan_axis_point z))
  (@cartan_lower_axis_identity_analytic R) (@cartan_lower_axis_coefficient_analytic R)
  (fun i k=>hAxisH i (2*k+parity)%N).
exists G;split;first exact:hG;split.
- apply:(@quadratic_cleared_remainder_jet_agreement R R^o N hN J
    (@cartan_arc_domain_interior R) parity order (fun z=>z) (fun z=>FlatExponential.value (1-z))
    (fun i k z=>P i (2*k+parity)%N (cartan_axis_point z))
    (fun i k z=>H i (2*k+parity)%N (cartan_axis_point z)) m 0 hJ0
    (@cartan_lower_axis_identity_analytic R) (@cartan_lower_axis_coefficient_analytic R)
    (fun i k=>hB i (2*k+parity)%N) (fun i k=>hAxisH i (2*k+parity)%N)).
  move=>i k hi hk.
  have hBound:(i+(2*k+parity+m)<=L)%N.
    have hSum:(i+2*k<=order+2*order)%N:=leq_add hi (leq_mul (leqnn 2) hk).
    have hThree:(order+2*order=3*order)%N by rewrite [RHS]mulSn addnC.
    have hAssoc:(i+(2*k+parity+m)=(i+2*k)+parity+m)%N by rewrite !addnA.
    rewrite hAssoc /L -hThree.
    exact:(leq_add (leq_add hSum (leqnn parity)) (leqnn m)).
  have hLower:=norm_finite_jet_agreement_lower hBound hAgree.
  have hFields:=@analytic_iterated_directional_finite_jet_agreement R X R^o NX N hNX hN
    setT U f g i (2*k+parity)%N m 0 (@coordinate_basis R 3 ord0) (@coordinate_basis R 3 j)
    (C i) (E i) (P i (2*k+parity)%N) (H i (2*k+parity)%N)
    Logic.I hU0 hf hg (hC i).1 (hE i).1 (hP i (2*k+parity)%N).1 (hH i (2*k+parity)%N).1 hLower.
  have hLocal:=@norm_finite_jet_agreement_local R X R^o NX N hNX hN Z ev NZ hZ
    U setT U (P i (2*k+parity)%N) (P i (2*k+parity)%N) m 0
    (@cartan_lower_domain_interior R) _ (fun v hv _=>erefl _) hU0.
  have hDomains v (hv:U v):U v <->setT v by split=>_;[exact:Logic.I|exact:hv].
  have hSame:=hLocal hDomains.
  exact:(cartan_axis_finite_jet_agreement (hPU i (2*k+parity)%N) (hH i (2*k+parity)%N).2
    (norm_finite_jet_agreement_transitive hSame hFields)).
- move=>t /andP[ht0 ht1].
  have hNonzero:t!=0 by rewrite (gt_eqF ht0).
  exact:(@cartan_multiple_cleared_remainder_zero R q D E B H parity order t hq
    (fun i=>(hD i).1) (fun i k=>(hBq i k).1) (fun i=>(hE i).1) (fun i k=>(hH i k).1)
    hParity ht1 hNonzero).
Qed.
End Remainders.
