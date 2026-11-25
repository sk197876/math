(** Federer (1969), 3.4.5, p. 321: finite
    actual jet divisibility by the adapted surface equation
    in the real proof of the cited local/global example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDifferentialUP NormBoundedLinearTopology NormOpenDomainLaws
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormAnalyticUP NormAnalyticLocal
  NormAnalyticDomain NormAnalyticOperations NormAnalyticArithmetic NormAnalyticScalarProducts
  NormDiffeomorphismUP NormJetUP PolynomialFunctions FlatExponentialSealed FlatExponentialOrder CartanSurfaceUP CartanSurfaceSealed
  CartanSurfaceEquation CartanNormalizationEquation CartanConePullback CubicConePolynomialDivisibility
  AnalyticCubicConeJetDivision FiniteInnerScalarPolynomialAnalytic NormFiniteJetAgreement
  NormFiniteJetAgreementOperations NormAnalyticFiniteJetPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Division.
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
Local Notation AN A f:=(@norm_analytic R X R^o NX N hNX hN A f).

(** Source for [cartan_surface_finite_jet_division]: for
    every finite order, an original global analytic function
    vanishing on the actual surface has the same actual
    finite jet at the origin as an analytic multiple
    of the original surface equation. The quotient exists
    locally and every actual derivative is compared. No
    convergent infinite quotient is assumed, supporting 3.4.5, p. 321. *)
Theorem cartan_surface_finite_jet_division (f:X->R) k:
  AN setT f ->(forall v,CartanSurface.set v ->f v=0) ->
  exists q:X->R,
    AN U q /\norm_finite_jet_agreement NX ev NZ setT U f
      (fun v=>q v*cartan_surface_equation v) k 0.
Proof.
move=>hf hZero.
have [T [G [r [hr [hRU [hT0 [hG0 [hX [hY [hZCoord [hT [hG [hInverse [hF [hV0 hCone]]]]]]]]]]]]]]]:=
  cartan_cone_pullback_exist hf hZero.
pose W:=[set v:X|NX v<r].
pose V:=T @` W.
pose F:=fun v:X=>f (G v).
have [P [Q [hP hFactor]]]:=@analytic_cubic_cone_finite_jet_division R NX hNX V F k.+1 hF hV0 hCone.
have hPoly (H:PolynomialFunction X R^o):AN setT H.
  exact:(@finite_inner_scalar_polynomial_analytic R X (@euclidean_inner_product R 3)
    (@euclidean_inner_productP R 3) 3%N (@coordinate_basis R 3) (@coordinate_basisP R 3) H).
have hU0:U 0 by rewrite /= ffunE;exact:ltr01.
have hTV0:V (T 0) by rewrite hT0.
have hPull:=@norm_analytic_finite_jet_pullback R X X R^o NX NX N hNX hNX hN U V T F k.+1 0 P
  (leq0n k) hU0 hTV0 hT hF (hPoly P).
have hPAtT:is_norm_jet_polynomial NX ev NZ V F k.+1 (T 0) P by rewrite hT0.
have hAgreement:=hPull hPAtT.
pose C:=fun v:X=>U v /\V (T v).
have hOpenW v (hv:W v):norm_domain_interior NX W v.
  have hSmall:NX (v-0)<r by rewrite subr0.
  have hh:norm_domain_interior NX [set w:X|NX (w-0)<r] v:=
    @norm_open_ball_domain_interior R X NX hNX 0 r v hSmall.
  have hS:[set w:X|NX (w-0)<r]=W by apply:funext=>w;rewrite /= subr0.
  by rewrite hS in hh.
have hW0:W 0 by rewrite /W /= (real_seminorm_zero hNX.1).
have hLocal:=@norm_finite_jet_agreement_local R X R^o NX N hNX hN Z ev NZ hZ
  setT C W f (fun v=>F (T v)) k.+1 0 hOpenW.
have hDomains v (hv:W v):setT v <->C v.
  split=>_;last exact:Logic.I.
  split;first exact:(hRU v hv).
  exact:(norm_diffeomorphism_maps hInverse hv).
have hValues v (hv:W v) (_:setT v):f v=F (T v).
  by rewrite /F (norm_diffeomorphism_left_inverse hInverse hv).
have hFirst:=hLocal hDomains hValues hW0.
have hWhole:=norm_finite_jet_agreement_transitive hFirst hAgreement.
pose H:=fun v:X=>P (T v).
pose q:=fun v:X=>-Q (T v)*(FlatExponential.value (1-v ord_max))^-1.
have hQComposite:AN U (fun v=>Q (T v)):=
  norm_analytic_compose_on (fun v (_:U v)=>Logic.I) hT (hPoly Q).
have hQNegative:AN U (fun v=>-Q (T v)).
  move=>v hv;have hs:=@norm_analytic_at_scale R X R^o NX N hNX hN U
    (fun w=>Q (T w)) v (-1) (hQComposite v hv).
  apply:(norm_analytic_at_domain_agreement _ hs)=>w _.
  change ((-1:R)*Q (T w)=-Q (T w));exact:mulN1r.
have hq:AN U q:=norm_analytic_scalar_product hQNegative (@cartan_inverse_coefficient_analytic R).
have hEquation v (hv:U v):H v=q v*cartan_surface_equation v.
  have hE:=cartan_normalization_equation hX hY hZCoord hv.
  change (cartan_surface_equation v= -FlatExponential.value (1-v ord_max)*cubic_cone_polynomial_value (T v)) in hE.
  rewrite /H /q hFactor hE.
  have hNonzero:FlatExponential.value (1-v ord_max)!=0.
    have hp:0<FlatExponential.value (1-v ord_max) by rewrite FlatExponentialOrder.flat_exponential_positive subr_gt0.
    by rewrite gt_eqF.
  by field.
have hFinal:=@norm_finite_jet_agreement_local R X R^o NX N hNX hN Z ev NZ hZ
  U U U H (fun v=>q v*cartan_surface_equation v) k.+1 0
  (@cartan_lower_domain_interior R) (fun v (_:U v)=>iff_refl _) (fun v hv _=>hEquation v hv) hU0.
exists q;split;first exact:hq.
apply:(norm_finite_jet_agreement_lower (leqnSn k)).
exact:(norm_finite_jet_agreement_transitive hWhole hFinal).
Qed.
End Division.
