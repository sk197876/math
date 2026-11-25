(** Federer (1969), 4.1.19, p. 377: if
    alpha is represented by phi and psi,
    then d alpha is represented by psi
    and zero. The two original q actions
    and the actual boundary-squared theorem suffice. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingPairing PairingLinear CurrentDomain CurrentCoefficientNorms
  FlatCurrentUnionSpace FlatCochainSpace FlatCochainCoboundary
  CompactSummableMultivectors CurrentLonePairImageUP CurrentLonePairFlatUP
  EuclideanOpenDomainMeasure MeasureIntegralUP MeasureAlmostBasic
  MeasureConullZeroIntegral PartialFunctionBasic SummableRealFunctionUP
  FlatCochainPairFunctional FlatCochainRepresentationUP
  FlatLonePairBoundary BoundedCurrentFormZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CoboundaryDensity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation P d := (@current_lone_pair_space R h2 n d U hU).
Local Notation W d := (@flat_current_union_space R h2 n d U hU).
Local Notation C d := (@flat_cochain_space R h2 n d U hU).
Local Notation E d := (@flat_cochain_evaluation R h2 n d U hU).
Local Notation beta d := (@flat_cochain_pair_functional R h2 n d U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Variable Q : Hom (P m) (W m).
Variable S : Hom (P m.+1) (W m.+1).
Hypothesis hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q.
Hypothesis hS : @is_current_lone_pair_flat_map R h2 n m.+1 U hU S.

(** Source for [flat_cochain_coboundary_form_density]:
    the last mathematical assertion of Federer
    4.1.19, p. 377: the
    coboundary is represented by psi and
    zero on the same original U.
    The arbitrary representing pair need only
    satisfy the two actual bounded measurable action laws. *)
Theorem flat_cochain_coboundary_form_density (alpha : C m)
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  @is_flat_cochain_pair_density R h2 n m U hU Q alpha phi psi ->
  @is_flat_cochain_pair_density R h2 n m.+1 U hU S
    (@flat_cochain_coboundary R h2 n m U hU alpha)
    psi (fun _ : UT => 0).
Proof.
move=> hDensity.
split; first exact: hDensity.2.1.
split; first exact: (@bounded_measurable_current_form_zero R h2 n m.+2 U hU).
split.
- move=> eta.
  rewrite flat_cochain_pair_functional_evaluation
    flat_cochain_coboundary_evaluation
    (@flat_lone_pair_density_boundary R h2 n m U hU Q S hQ hS eta).
  exact: (hDensity.2.2.2 eta).
- move=> zeta.
  rewrite flat_cochain_pair_functional_evaluation
    flat_cochain_coboundary_evaluation
    (@flat_lone_pair_boundary_squared R h2 n m U hU S hS zeta) linear0.
  apply: (@measure_almost_zero_integral R UT mu hMu).
  apply: (@measure_almost_everywhere_mono R UT mu hMu setT _ _
    (measure_almost_everywhere_true hMu))=> x _.
  apply/real_total_integrand_graph.
  change ((pairing_right (value m.+2 zeta x) 0)%:E=0%E).
  by rewrite linear0.
Qed.
End CoboundaryDensity.
