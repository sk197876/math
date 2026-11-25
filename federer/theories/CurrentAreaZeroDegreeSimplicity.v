(** Federer (1969), 4.1.25, p. 383: check
    the unqualified simplicity sentence against the
    literal empty-product convention of 1.6.1,
    pp. 23–24. The actual zero Omega field
    on R^0 and a constant Lipschitz map have
    the actual fibre density zero, which is not
    the empty product one. The associated-plane
    and signed statements for a nonzero density
    are unaffected by this boundary calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormOpenDomainLaws GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ExteriorGrading ExteriorPowers ExteriorMaps AssociatedSubspace
  SimpleZeroDegree
  CurrentCoefficientNorms CompactSummableMultivectors CompactSummableMultivectorAmbient
  CompactSummableMultivectorDifference LipschitzUP LipschitzBasic
  EuclideanLinearJacobian PartialFunctionUP PartialFunctionExtensionUP
  NonnegativeSum NonnegativeSumSupport CurrentAreaNormalisedImageUP
  CurrentAreaNormalisedImageSealed CurrentAreaFibreSumUP CurrentAreaFibreSumExistence
  CurrentAreaFibreSumZero CurrentAreaFibreDensitySealed
  HausdorffMeasure HausdorffZeroNullEmpty MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroDegreeSimplicity.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Local Notation X := (R_n R 0%N).
Local Notation XT := (inner_metric_space (@euclidean_inner_productP R 0%N)).
Local Notation V := (exterior_power X 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Omega := (@compact_summable_multivector_space R h2 0%N 0%N Full hFull).
Local Notation source := (0 : Omega).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 0%N 0%N Full hFull source).
Local Notation f := (fun _ : X => (0 : X)).
Local Notation u := (@CurrentAreaNormalisedImage.value R 0%N 0%N f raw).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X 0%N 0%N f u).
Local Notation H := (@hausdorff_measure R XT 0%N).

(** Source for [current_area_zero_degree_map_lipschitz]:
    the constant map in the degree-zero boundary
    of Federer 4.1.25, p. 383, satisfies
    its original Lipschitz hypothesis by 2.2.7. *)
Lemma current_area_zero_degree_map_lipschitz :
  @is_metric_lipschitz R XT XT setT f.
Proof.
apply: metric_lipschitz_of_bound.
exact: least_metric_lipschitz_bound (metric_lipschitz_constant_map setT (0 : XT)).
Qed.

(** Source for [current_area_zero_degree_source_zero]:
    the actual zero field of Omega_0, not a
    separately postulated representative, in the
    boundary calculation for 4.1.25, p. 383. *)
Lemma current_area_zero_degree_source_zero x : raw x = 0.
Proof.
have h := congr1 (fun g => g x)
  (@compact_summable_multivector_ambient_difference R h2 0%N 0%N Full hFull source source).
by move: h; rewrite !subrr.
Qed.

(** Source for [current_area_zero_degree_summand_zero]:
    every original normalized differential summand
    is defined and zero for this actual zero
    source, supporting the 4.1.25 boundary example.
    J_0=1, so no singular quotient is introduced. *)
Lemma current_area_zero_degree_summand_zero x :
  partial_function_graph u x (0 : V).
Proof.
apply: (@CurrentAreaNormalisedImage.laws R 0%N 0%N f raw x 0%R).2.
exists (0 : Hom X X); split.
- exact: (@norm_differential_constant R X X NX NX hNX hNX Full x 0%R
    (norm_full_domain_interior NX x)).
- split; first by rewrite euclidean_linear_jacobian_zero_degree oner_eq0.
  by rewrite /current_area_normalised_image_coefficient
    current_area_zero_degree_source_zero linear0 scaler0.
Qed.

(** Source for [current_area_zero_degree_density_zero]:
    the actual original full-fibre density of
    Federer 4.1.25, p. 383, is defined and
    zero at every target point in this example.
    Its existence is proved from the exact
    original summands and their finite mass sum. *)
Theorem current_area_zero_degree_density_zero y :
  partial_function_graph eta y (0 : V).
Proof.
have hExtension : is_partial_function_total_extension u (fun _ : X => (0 : V)).
  move=> x v hValue.
  exact: partial_function_single_valued (current_area_zero_degree_summand_zero x) hValue.
have hDomain x : f x = y -> partial_function_domain u x.
  move=> _; exists 0%R; exact: current_area_zero_degree_summand_zero.
have hFinite : (nonnegative_sum [set x | f x = y]
    (fun _ : X => (@current_vector_mass R h2 0%N 0%N (0 : V)%R)%:E) < +oo)%E.
  rewrite (real_seminorm_zero (@current_vector_mass_real_norm R h2 0%N 0%N).1).
  rewrite (nonnegative_sum_zero (fun x (_ : f x = y) => erefl (0 : \bar R))).
  exact: ltry.
have [v hSum] := @current_area_fibre_sum_exists R h2 X 0%N 0%N f u
  (fun _ : X => (0 : V)) y hExtension hDomain hFinite.
have hZero : v = 0.
  apply: (@current_area_fibre_sum_zero R h2 X 0%N 0%N f u y v hSum).
  move=> x a _ hValue; exact: esym (hExtension x a hValue).
apply: (@CurrentAreaFibreDensity.laws R h2 X 0%N 0%N f u y 0%R).2.
by rewrite -hZero.
Qed.

(** Source for [current_area_zero_degree_simplicity_counterexample]:
    the unqualified simplicity sentence of Federer
    4.1.25, p. 383, fails for the actual
    zero Omega_0 field. H^0 has no nonempty
    null sets by 2.10.2, p. 171. Thus
    the failed simplicity assertion cannot be repaired
    by changing the density on a null set. *)
Theorem current_area_zero_degree_simplicity_counterexample :
  ~ measure_almost_everywhere H [set y | exists v : V,
    partial_function_graph eta y v /\ simple v].
Proof.
have hNotSimple : ~simple (0 : V).
  have hScalar := @scalar_not_simple R X 0%R.
  rewrite linear0 in hScalar.
  apply: hScalar; by rewrite eq_sym oner_eq0.
move=> hAlmost.
pose P := [set y | exists v : V, partial_function_graph eta y v /\ simple v].
have hEmpty : ~` P = set0 := @hausdorff_zero_null_set_empty R XT (~` P) hAlmost.
have hOutside : (~` P) (0 : X).
  move=> [v [hValue hSimple]].
  have hZero := partial_function_single_valued
    (current_area_zero_degree_density_zero (0 : X)) hValue.
  apply: hNotSimple; by rewrite hZero.
have hImpossible : set0 (0 : X) by rewrite -hEmpty.
exact: hImpossible.
Qed.
End ZeroDegreeSimplicity.
