(** Federer (1969), 4.1.19, p. 377:
    the dual pair norm for arbitrary bounded
    measurable representatives is the maximum of
    their essential comasses. Selected pointwise-bounded
    representatives are treated separately; the literal
    earlier global comass is not redefined. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CurrentLonePairImageUP CurrentLonePairCost
  CompactSummableMultivectors EuclideanOpenDomainMeasure PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostEquality MeasureEssentialNorm
  MeasureEssentialNormComparison RealFunctionalNormUP FlatCochainRepresentationUP
  FlatCochainRepresentativeNorm BoundedPairFormRepresentation BoundedPairFormFunctional
  BoundedCurrentFormEssentialRepresentative FlatCochainFormAlmostUniqueness
  LonePairFormDensityAlmost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EssentialPairNorm.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation pairnorm phi psi :=
  (flat_cochain_representative_norm mu (N m) (N m.+1)
    (partial_function_total phi) (partial_function_total psi)).

(** Source for [lone_pair_form_density_functional_bound]:
    any common pointwise comass bound gives
    the same beta bound, supporting the
    norm display of Federer 4.1.19,
    p. 377. The original action laws
    identify beta with the proved bounded
    integral functional; no representation norm is assumed. *)
Theorem lone_pair_form_density_functional_bound (beta : Hom P R^o)
    (phi : UT -> Y m) (psi : UT -> Y m.+1) (c : R) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  0 <= c -> (forall x, N m (phi x) <= c) ->
  (forall x, N m.+1 (psi x) <= c) ->
  forall v, `|beta v| <= c*J v.
Proof.
move=> hDensity hC hPhiCap hPsiCap.
have [gamma [hBound hGamma]] := @bounded_pair_form_functional_with_bound_exists
  R h2 n m U hU phi psi c hC hDensity.1 hDensity.2.1 hPhiCap hPsiCap.
have hEqual := @lone_pair_form_functional_unique R h2 n m U hU
  beta gamma phi psi hDensity hGamma.
by rewrite hEqual.
Qed.

(** Source for [lone_pair_form_density_essential_upper]:
    the exact beta norm bounds both
    essential comasses of any representing pair,
    supporting Federer 4.1.19, p. 377.
    First choose the sharp bounded representatives,
    then use the independently proved almost uniqueness. *)
Theorem lone_pair_form_density_essential_upper (beta : Hom P R^o)
    (phi : UT -> Y m) (psi : UT -> Y m.+1) (a : R) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  is_real_functional_norm J (hom_as_linear beta) a ->
  (pairnorm phi psi <= a%:E)%E.
Proof.
move=> hDensity hNorm.
have hA := real_functional_norm_nonnegative hNorm.
have [phi0 [psi0 [hSelected [hPhiCap hPsiCap]]]] :=
  @bounded_lone_pair_form_representation R h2 n m U hU beta a hA
    (real_functional_norm_bound hNorm).
have [hPhi hPsi] := @lone_pair_form_density_almost_unique R h2 n m U hU
  beta phi phi0 psi psi0 hDensity hSelected.
have hPhiPartial := (@measure_almost_equal_total R UT (Y m) mu phi phi0).2 hPhi.
have hPsiPartial := (@measure_almost_equal_total R UT (Y m.+1) mu psi psi0).2 hPsi.
have hEqual := @flat_cochain_representative_norm_almost_equal R UT (Y m) (Y m.+1)
  mu hMu (N m) (N m.+1) (partial_function_total phi)
  (partial_function_total phi0) (partial_function_total psi)
  (partial_function_total psi0) hPhiPartial hPsiPartial.
rewrite hEqual /flat_cochain_representative_norm ge_max.
apply/andP; split.
- exact: (@bounded_current_form_essential_bound R h2 n m U hU phi0 a hA hPhiCap).
- exact: (@bounded_current_form_essential_bound R h2 n m.+1 U hU psi0 a hA hPsiCap).
Qed.

(** Source for [lone_pair_form_density_essential_norm]:
    the exact dual norm of beta equals
    the maximum of the two essential
    comasses, supporting the norm display in
    Federer 4.1.19, p. 377.
    Arbitrary bounded measurable representatives and
    empty original domains retain the same equality. *)
Theorem lone_pair_form_density_essential_norm (beta : Hom P R^o)
    (phi : UT -> Y m) (psi : UT -> Y m.+1) (a : R) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  is_real_functional_norm J (hom_as_linear beta) a ->
  a%:E=pairnorm phi psi.
Proof.
move=> hDensity hNorm.
have hUpper := lone_pair_form_density_essential_upper hDensity hNorm.
have [b [phi0 [hB [hPhiNorm [hPhi0 [hPhiCap hPhiAlmost]]]]]] :=
  @bounded_current_form_essential_representative R h2 n m U hU phi hDensity.1.
have [c [psi0 [hC [hPsiNorm [hPsi0 [hPsiCap hPsiAlmost]]]]]] :=
  @bounded_current_form_essential_representative R h2 n m.+1 U hU psi hDensity.2.1.
pose bound := Order.max b c.
have hBBound : b <= bound by rewrite /bound le_max lexx.
have hCBound : c <= bound by rewrite /bound le_max lexx orbT.
have hBound : 0 <= bound := le_trans hB hBBound.
have hPhiBound x : N m (phi0 x) <= bound.
  exact: (le_trans (hPhiCap x) hBBound).
have hPsiBound x : N m.+1 (psi0 x) <= bound.
  exact: (le_trans (hPsiCap x) hCBound).
have hNew := @lone_pair_form_density_almost_invariant R h2 n m U hU
  beta phi phi0 psi psi0 hDensity hPhi0 hPsi0 hPhiAlmost hPsiAlmost.
have hBetaBound := @lone_pair_form_density_functional_bound beta phi0 psi0 bound
  hNew hBound hPhiBound hPsiBound.
have hLeast := real_functional_norm_least hNorm hBound hBetaBound.
apply/eqP; rewrite eq_le hUpper andbT.
rewrite /flat_cochain_representative_norm hPhiNorm hPsiNorm -EFin_max lee_fin.
exact: hLeast.
Qed.
End EssentialPairNorm.
