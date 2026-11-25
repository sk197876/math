(** Supporting Federer (1969), 3.4.8(5), p. 328:
    compare two original finite analytic coefficient rings of one
    local quotient. Exact finite Taylor interpolation and the existing
    Noetherian module, Artin--Rees and dimension theorems prove the bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives
  AnalyticGermDomain AnalyticGermNoetherian AnalyticScalarsSealed AnalyticGermValueSealed
  AnalyticVanishingIdealSealed AnalyticVanishingIdealLaws RingScalarRestriction RingSubmoduleUP
  CommutativeIdealUP CommutativeIdealSealed CommutativeDomainUP FractionFieldSealed
  CommutativeQuotientUP CommutativeQuotientSealed CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  CommutativeFactorizationUP FiniteModuleNontorsionFunctional PrincipalAdicShift FiniteAlgebraResidueFiltration
  FiniteModuleFreeCover FiniteJetDegreeIndices FiniteJetDegreeLowerCount AnalyticFiniteTaylorMaps
  FiniteAdicQuotientInjection FiniteAdicQuotientCover FiniteFreeLinearComparison NaturalPolynomialGrowthDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Dimension.
Variable R:realType.
Local Notation X:=(R_n R).
Local Notation B:=(fun s=>@euclidean_inner_product R s).
Local Notation hB:=(fun s=>@euclidean_inner_productP R s).
Local Notation NX:=(fun s=>inner_norm (hB s)).
Local Notation hNX:=(fun s=>inner_norm_real_norm (hB s)).
Local Notation A:=(fun s=>[the comNzRingType of (@analytic_germ_ring R (X s) (NX s) (hNX s) 0)]).
Local Notation constants:=(fun s=>@AnalyticScalars.map R (X s) (NX s) (hNX s) 0).
Local Notation residue:=(fun s=>@AnalyticGermValue.map R (X s) (NX s) (hNX s) 0).
Local Notation ideal:=(fun s=>@AnalyticVanishingIdeal.value R (X s) (NX s) (hNX s) 0).
Local Notation F:=(fun s l=>@finite_analytic_taylor_coefficients R (X s) (B s) (hB s)
  s (@coordinate_basis R s) l).
Local Notation T:=(fun s l=>@finite_analytic_taylor_section R (X s) (B s) (hB s)
  s (@coordinate_basis R s) (@coordinate_basisP R s) l).

(** Source for [finite_analytic_coefficient_dimension]: supporting
    the original arbitrary-ideal auxiliary assertion of Federer
    3.4.8(5), p. 328. A faithful m-coordinate action finite over the
    original analytic germ ring cannot exceed any other finite
    d-coordinate action on the same local quotient. No primeness,
    reducedness or geometric vanishing-ideal premise is imposed. *)
Theorem finite_analytic_coefficient_dimension m d (C:comNzRingType)
    (phi:{rmorphism A m->C}) (psi:{rmorphism A d->C}) (scalar:{rmorphism R->C}) (M:set C):
  (forall c:R,phi (constants m c) = scalar c) ->
  (forall c:R,psi (constants d c) = scalar c) ->
  is_commutative_ideal M ->~M 1 ->
  (forall c:C,M c ->is_commutative_unit (1-c)) ->
  (forall a:A m,ideal m a ->M (phi a)) ->
  (forall a:A d,ideal d a ->M (psi a)) ->
  injective phi ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType (A m) of ring_restricted_space phi C^o]) ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType (A d) of ring_restricted_space psi C^o]) ->(m<=d)%N.
Proof.
move=>hPhiConstants hPsiConstants hM hProper hUnit hPhiIdeal hPsiIdeal hFaithful hFiniteM hFiniteD.
have hDomain:is_commutative_integral_domain (A m):=
  @analytic_germ_no_zero_divisors R (X m) (NX m) (hNX m) 0.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R (X m) (NX m) (hNX m)
  m (@coordinate_basis R m) 0 (@coordinate_basisP R m).
have hTorsion a:a*:(1:[the lmodType (A m) of ring_restricted_space phi C^o]) = 0 ->a = 0.
  change (phi a*1 = 0 ->a = 0);rewrite mulr1=>hZero.
  apply:hFaithful;by rewrite hZero rmorph0.
have [L hDelta]:=@finite_module_nontorsion_functional (A m) (@FractionField.space (A m) hDomain)
  (@FractionField.embed (A m) hDomain)
  [the lmodType (A m) of ring_restricted_space phi C^o] 1
  (@FractionField.laws (A m) hDomain) hDomain hFiniteM hTorsion.
have hIdeal:=@analytic_vanishing_ideal_is_ideal R (X m) (NX m) (hNX m) 0.
have [r0 hShift]:=@nonzero_principal_adic_shift (A m) (ideal m) (L 1)
  hNoetherian hDomain hIdeal hDelta.
pose J:=@GeneratedCommutativeIdeal.value C (phi @` ideal m).
have hJ:=@GeneratedCommutativeIdeal.laws C (phi @` ideal m).
have hResidueConstants c:residue m (constants m c) = c.
  by rewrite (@AnalyticScalars.laws R (X m) (NX m) (hNX m) 0 c)
    (@AnalyticGermValue.laws R (X m) (NX m) (hNX m) 0).
have [b [hPositiveBlock hBlock]]:=@finite_algebra_residue_filtration R (A m) C
  (constants m) (residue m) phi scalar (ideal m) M J hResidueConstants hPhiConstants
  (@AnalyticVanishingIdeal.laws R (X m) (NX m) (hNX m) 0)
  hM hProper hUnit hPhiIdeal hJ hFiniteM.
have [N [e hCover]]:=@finite_module_free_cover (A d)
  [the lmodType (A d) of ring_restricted_space psi C^o] hFiniteD.
apply:(@natural_polynomial_growth_dimension m d N (b * m)%N (b * (r0+1))%N)=>r hPositiveR.
pose l:=(m * r).+1.
pose q:=(b * (r0+l))%N.
have hPositiveQ:(0<q)%N by rewrite /q muln_gt0 hPositiveBlock addn_gt0 /l ltn0Sn orbT.
have hPowerProper:~@CommutativeIdealPowers.value C M q 1.
  move=>hOne;apply:hProper.
  have hLower:=@commutative_ideal_power_antitone C M 1%N q hPositiveQ 1 hOne.
  by rewrite (commutative_ideal_power_oneE hM) in hLower.
have hPowerIdeal:=@commutative_ideal_power_is_ideal C M q.
pose Q:=@CommutativeIdealQuotient.space R C scalar
  (@CommutativeIdealPowers.value C M q) hPowerIdeal hPowerProper.
pose rho:=@CommutativeIdealQuotient.projection R C scalar
  (@CommutativeIdealPowers.value C M q) hPowerIdeal hPowerProper.
have hRho:=@CommutativeIdealQuotient.laws R C scalar
  (@CommutativeIdealPowers.value C M q) hPowerIdeal hPowerProper.
have [f hInjective]:=@finite_adic_quotient_injection R (A m) C Q (constants m) phi scalar rho
  (ideal m) M J b r0 l (finite_jet_degree_indices m l) L (F m l) (T m l)
  hPhiConstants hJ hBlock (hShift l)
  (@finite_analytic_taylor_kernel R (X m) (B m) (hB m) m
    (@coordinate_basis R m) (@coordinate_basisP R m) l)
  (@finite_analytic_taylor_interpolation R (X m) (B m) (hB m) m
    (@coordinate_basis R m) (@coordinate_basisP R m) l) hRho.
have [g hOnto]:=@finite_adic_quotient_cover R (A d) C Q (constants d) psi scalar rho
  (ideal d) M q N e (finite_jet_degree_indices d q) (F d q) (T d q)
  hPsiConstants hM hPsiIdeal hRho hCover
  (@finite_analytic_taylor_remainder R (X d) (B d) (hB d) d
    (@coordinate_basis R d) (@coordinate_basisP R d) q).
have hCard:=finite_function_injection_cover_card hInjective hOnto.
rewrite card_prod card_ord in hCard.
have hCount:(r ^ m<=N*q ^ d)%N.
  apply:(leq_trans (@finite_jet_degree_card_lower m r)).
  apply:(leq_trans hCard).
  exact:(leq_mul (leqnn N) (@finite_jet_degree_card_upper d q)).
have hQ:q = ((b * m) * r+b * (r0+1))%N.
  by rewrite /q /l -addn1 [(r0+(m * r+1))%N]addnCA mulnDr mulnA.
by rewrite -hQ.
Qed.
End Dimension.
