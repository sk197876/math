(** Supporting Federer (1969), 3.4.8(5), p. 328:
    exact original polynomial germ derivatives. Reuse the actual
    polynomial differential fields of 3.1.11, p. 221 and the
    original coefficient-at-zero law of 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  NormDifferentialUP NormLinearDomainLaws NormOpenDomainLaws ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialUnique PolynomialFunctions PolynomialRepresentations
  PolynomialTaylor PolynomialTaylorExactExpansion SymmetricForms SymmetricFormSum
  FiniteInnerPolynomialSmoothness AnalyticGermRepresentatives AnalyticGermRing
  AnalyticGermJetsSealed AnalyticPolynomialGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Jets.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation NS:=(fun z:R^o=>`|z|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun k=>@ContinuousMultilinear.space R k X R^o NX NS hNX hNS).
Local Notation ev:=(fun k=>@ContinuousMultilinear.evaluation R k X R^o NX NS hNX hNS).
Local Notation NZ:=(fun k=>@ContinuousMultilinear.norm R k X R^o NX NS hNX hNS).
Local Notation hZ:=(fun k=>@ContinuousMultilinear.laws R k X R^o NX NS hNX hNS).

(** Source for [analytic_polynomial_germ_jet_values]: supporting
    actual polynomial jet interpolation for Federer 3.4.8(5), p. 328.
    Every original derivative is precisely the already proved
    polynomial Taylor coefficient of 3.1.11, p. 221. *)
Theorem analytic_polynomial_germ_jet_values a
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX a)
    (hJ:is_analytic_polynomial_germ_map J) (P:PolynomialFunction X R^o) k u:
  ev k u (@AnalyticGermJets.value R X NX hNX a k (J P)) =
    polynomial_taylor_coefficient P k a [tuple u i | i<k].
Proof.
have [p [hValues hGerm]]:=hJ P.
have [D [hDValues hD]]:=@finite_inner_polynomial_differential_fields R X R^o B hB NS hNS
  n e he Z ev NZ hZ setT (fun x _=>@norm_full_domain_interior R X NX x) P.
have hJet:=@AnalyticGermJets.laws R X NX hNX a k (J P) p (esym hGerm).
have hFunctions:analytic_representative_value p = P:=funext hValues.
rewrite hFunctions in hJet.
have hEqual:=@norm_higher_differential_unique R X R^o NX NS hNX hNS Z ev NZ hZ
  setT P k a _ _ hJet (hD k a Logic.I).
rewrite hEqual;exact:hDValues k a u.
Qed.

(** Source for [analytic_polynomial_germ_origin_coefficients]: supporting
    exact finite coefficient interpolation for Federer 3.4.8(5), p. 328.
    At zero the original polynomial germ jet is its original homogeneous
    coefficient form; no replacement Taylor coefficients are introduced. *)
Theorem analytic_polynomial_germ_origin_coefficients
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0)
    (hJ:is_analytic_polynomial_germ_map J) (P:PolynomialFunction X R^o) k u:
  ev k u (@AnalyticGermJets.value R X NX hNX 0 k (J P)) =
    sform_component k (polynomial_to_forms P) [tuple u i | i<k].
Proof.
rewrite (@analytic_polynomial_germ_jet_values 0 J hJ P k u)
  (@polynomial_taylor_coefficient_at_zero R (@pchar_num R) X R^o P k).
reflexivity.
Qed.
End Jets.
