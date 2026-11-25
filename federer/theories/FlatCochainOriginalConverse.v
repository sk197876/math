(** Federer (1969), 4.1.19, p. 377: the
    original weak bounded measurable pair determines
    a unique actual flat cochain, with the sharp
    essential pair norm. The preceding item supplies
    the actual onto map, costs and kernel closure. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms FlatCochainSpace
  CurrentLonePairImageUP CurrentLonePairImageSealed CurrentLonePairCost
  CurrentLonePairFlatSealed CurrentLonePairFlatSurjective
  CurrentLonePairKernelClosure CurrentCompactSmoothDivergenceUP
  FlatCochainOriginalPairCosts FlatCochainOriginalRepresentation
  FlatCochainWeakPairConverse FlatCochainRepresentationUP
  FlatCochainRepresentativeNorm CurrentWeakExteriorPairUP
  EuclideanOpenDomainMeasure PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section OriginalConverse.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation raw := (@CurrentLonePair.map R h2 n m U hU).
Local Notation Q := (@CurrentLonePairFlat.map R h2 n m U hU).
Local Notation hQ := (@CurrentLonePairFlat.laws R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation F := (@flat_cochain_norm R h2 n m U hU).
Local Notation density := (@is_flat_cochain_pair_density R h2 n m U hU Q).
Local Notation mu := (@euclidean_open_domain_measure R n U).

(** Source for [flat_cochain_original_weak_pair_converse]:
    the full converse assertion of Federer
    4.1.19, p. 377, for bounded measurable
    forms on arbitrary open U. There is no
    caller-supplied map, surjectivity, kernel condition,
    representation of currents or finite-volume premise. *)
Theorem flat_cochain_original_weak_pair_converse
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  @is_bounded_measurable_current_form R h2 n U m phi ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi ->
  @is_weak_current_exterior_pair R h2 n m U hU phi psi ->
  exists alpha : A,
    density alpha phi psi /\
    (F alpha)%:E=flat_cochain_representative_norm mu
      (@current_form_comass R h2 n m) (@current_form_comass R h2 n m.+1)
      (partial_function_total phi) (partial_function_total psi) /\
    forall gamma : A, density gamma phi psi -> gamma=alpha.
Proof.
move=> hPhi hPsi hWeak.
have hClosure (v : P) (hv : raw v=0) : forall epsilon : R, 0<epsilon ->
    exists w : P, @is_current_compact_smooth_divergence_pair R h2 n m U hU w /\
      J (v-w)%R<epsilon.
  exact: ((@current_lone_pair_kernel_graph_iff R h2 n m U hU v).1 hv).
have [alpha [hDensity hUnique]] := @flat_cochain_weak_pair_converse R h2 n m U hU
  Q hQ (@current_lone_pair_flat_surjective R h2 n m U hU)
  (@flat_cochain_original_pair_second_cost R h2 n m U hU) hClosure
  phi psi hPhi hPsi hWeak.
exists alpha; split; first exact: hDensity.
split; last exact: hUnique.
exact: (@flat_cochain_original_form_essential_norm R h2 n m U hU
  alpha phi psi hDensity).
Qed.
End OriginalConverse.
