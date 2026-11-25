(** Federer (1969), 4.1.19, p. 377:
    the converse starts with two bounded
    measurable forms and integrates them on
    the original Omega factors. Their sum
    is the actual bounded pair functional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentVectorCompleteness CurrentCovectorDual
  EuclideanOpenDomainMeasure CurrentLonePairImageUP CurrentLonePairCost
  CompactSummableMultivectors FlatCochainRepresentationUP
  CompactSummableDualFunctional.
From Federer Require Import MeasureIntegralUP SummableRealFunctionUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section FormFunctional.
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
Local Notation O d := (@compact_summable_multivector_space R h2 n d U hU).
Local Notation Y d := (A_m X R^o d).
Local Notation MN d := (@current_vector_mass R h2 n d).
Local Notation hMN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation YN d := (@current_form_comass R h2 n d).
Local Notation hYN d := (@current_form_comass_real_norm R h2 n d).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).

(** Source for [bounded_pair_form_functional_with_bound_exists]:
    the pair functional in the converse of
    Federer 4.1.19, p. 377,
    retains any common comass bound c for
    its two actual measurable forms. All
    original Omega actions have their stated finite integrals. *)
Theorem bounded_pair_form_functional_with_bound_exists
    (phi : UT -> Y m) (psi : UT -> Y m.+1) (c : R) :
  0 <= c ->
  @is_bounded_measurable_current_form R h2 n U m phi ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  (forall x, YN m (phi x) <= c) ->
  (forall x, YN m.+1 (psi x) <= c) ->
  exists beta : Hom P R^o,
    (forall v, `|beta v| <= c*J v) /\
    @is_lone_pair_form_density R h2 n m U hU beta phi psi.
Proof.
move=> hC hPhi hPsi hPhiBound hPsiBound.
have [F [hFAction hFBound]] := @compact_summable_dual_functional_exists
  R UT (exterior_power X m) (Y m) (MN m) (hMN m)
  (@current_covector_evaluation R n m) (YN m) (hYN m)
  (@current_covector_continuous_dual R h2 n m)
  (@current_multivector_mass_separable R h2 n m)
  (@current_form_separable R h2 n m) mu hMu phi c hC hPhi.1 hPhiBound.
have [G [hGAction hGBound]] := @compact_summable_dual_functional_exists
  R UT (exterior_power X m.+1) (Y m.+1) (MN m.+1) (hMN m.+1)
  (@current_covector_evaluation R n m.+1) (YN m.+1) (hYN m.+1)
  (@current_covector_continuous_dual R h2 n m.+1)
  (@current_multivector_mass_separable R h2 n m.+1)
  (@current_form_separable R h2 n m.+1) mu hMu psi c hC hPsi.1 hPsiBound.
pose f := fun v : P => F v.1+G v.2.
have hLinear : linear f.
  move=> t v w; rewrite /f /= !hom_linear.
  change ((t*F v.1+F w.1)+(t*G v.2+G w.2)=
    t*(F v.1+G v.2)+(F w.1+G w.2)).
  by rewrite mulrDr addrACA.
pose beta := @HomMap R P R^o f (introT (asboolP _) hLinear).
exists beta; split.
- move=> v.
  have h := lerD (hFBound v.1) (hGBound v.2).
  rewrite -mulrDr in h.
  exact: (le_trans (ler_normD _ _) h).
split; first exact: hPhi.
split; first exact: hPsi.
split.
- move=> xi.
  change (is_measure_integral mu (real_total_integrand (fun x : UT =>
    pairing (@compact_summable_multivector_value R h2 n m U hU xi x) (phi x)))
    (F xi+G 0)%:E).
  rewrite (lin0 (hom_linear G)) addr0; exact: (hFAction xi).
- move=> eta.
  change (is_measure_integral mu (real_total_integrand (fun x : UT =>
    pairing (@compact_summable_multivector_value R h2 n m.+1 U hU eta x) (psi x)))
    (F 0+G eta)%:E).
  rewrite (lin0 (hom_linear F)) add0r; exact: (hGAction eta).
Qed.

(** Source for [bounded_pair_form_functional_exists]:
    every bounded measurable pair in the
    converse of Federer 4.1.19, p. 377,
    determines a bounded linear beta with
    the two literal original integral actions.
    Kernel annihilation is proved separately from
    the weak equation; it is not assumed here. *)
Theorem bounded_pair_form_functional_exists
    (phi : UT -> Y m) (psi : UT -> Y m.+1) :
  @is_bounded_measurable_current_form R h2 n U m phi ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  exists beta : Hom P R^o, exists c : R,
    0 <= c /\ (forall v, `|beta v| <= c*J v) /\
    @is_lone_pair_form_density R h2 n m U hU beta phi psi.
Proof.
move=> hPhi hPsi.
have [a [hA hPhiCap]] := hPhi.2.
have [b [hB hPsiCap]] := hPsi.2.
pose c := Order.max a b.
have hAC : a<=c by rewrite /c le_max lexx.
have hBC : b<=c by rewrite /c le_max lexx orbT.
have hC : 0 <= c := le_trans hA hAC.
have hPhiBound x : YN m (phi x) <= c.
  exact: (le_trans (hPhiCap x) hAC).
have hPsiBound x : YN m.+1 (psi x) <= c.
  exact: (le_trans (hPsiCap x) hBC).
have [beta [hBound hDensity]] :=
  @bounded_pair_form_functional_with_bound_exists phi psi c hC
    hPhi hPsi hPhiBound hPsiBound.
exists beta,c; split; first exact: hC.
by split.
Qed.
End FormFunctional.
