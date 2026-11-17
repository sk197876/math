(** Federer (1969), 3.4.8(14), p. 336:
    multiply the actual directional witnesses from the
    irreducible components. Existing least-order selection,
    original germ coefficient convolution and the initial
    coefficient identity prove a positive nonzero derivative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermRing AnalyticGermJetsSealed AnalyticReductionLociUP
  WeierstrassRegularUP WeierstrassRegularCoefficients AnalyticDirectionalRegularOrder
  AnalyticGermDirectionalCoefficient AnalyticGermDirectionalProduct NaturalConvolution
  NaturalConvolutionInitialCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_directional_product_nonzero]: the
    original product Phi in 3.4.8(14), p. 336,
    has a positive nonzero derivative in the same
    direction as its factors. Vanishing centre values
    are essential and follow from proper ideal membership. *)
Theorem analytic_directional_product_nonzero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (alpha beta:[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]) v:
  @AnalyticGermJets.value R X NX hNX 0 0%N alpha=0 ->
  @AnalyticGermJets.value R X NX hNX 0 0%N beta=0 ->
  has_nonzero_analytic_directional_jet alpha v ->
  has_nonzero_analytic_directional_jet beta v ->
  has_nonzero_analytic_directional_jet (alpha*beta) v.
Proof.
move=>hA0 hB0 hA hB.
have [k hK]:=analytic_directional_regular_order_exists hA0 hA.
have [l hL]:=analytic_directional_regular_order_exists hB0 hB.
pose a i:=@analytic_germ_directional_coefficient R X NX hNX 0 i alpha v.
pose b i:=@analytic_germ_directional_coefficient R X NX hNX 0 i beta v.
have hLowA i (hi:(i<k)%N):a i=0.
  by rewrite /a /analytic_germ_directional_coefficient (hK.2.1 i hi) mulr0.
have hLowB i (hi:(i<l)%N):b i=0.
  by rewrite /b /analytic_germ_directional_coefficient (hL.2.1 i hi) mulr0.
have hANonzero:a k<>0:=weierstrass_regular_leading_nonzero hK.
have hBNonzero:b l<>0:=weierstrass_regular_leading_nonzero hL.
have hCoefficient:@analytic_germ_directional_coefficient R X NX hNX 0 (k+l)%N (alpha*beta) v=a k*b l.
  rewrite analytic_germ_directional_coefficient_product.
  have hSum:(\sum_(j<(k+l).+1) a (k+l-j)%N*b j)=
      natural_coefficient_convolution b a (l+k)%N.
    rewrite [(l+k)%N]addnC /natural_coefficient_convolution big_mkord.
    apply:eq_bigr=>j _;exact:mulrC.
  rewrite hSum (natural_convolution_initial_coefficient hLowB hLowA);exact:mulrC.
exists (k+l)%N;split.
- have hKLe:(k<=k+l)%N by rewrite leq_addr.
  exact:leq_trans hK.1 hKLe.
- move=>hZero.
  have hProductZero:a k*b l=0.
    rewrite -hCoefficient /analytic_germ_directional_coefficient hZero mulr0;reflexivity.
  have /orP [hAZero|hBZero]:(a k==0)||(b l==0).
    by rewrite -mulf_eq0 hProductZero eqxx.
  + exact:hANonzero (elimT eqP hAZero).
  + exact:hBNonzero (elimT eqP hBZero).
Qed.
