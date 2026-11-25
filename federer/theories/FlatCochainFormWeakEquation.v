(** Federer (1969), 4.1.19, p. 377: both
    forms representing alpha satisfy the original
    weak derivative equation. The induced beta
    annihilates q-zero pairs; the preceding
    item proves every original compact smooth
    divergence pair has exactly zero q-image. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain FlatCurrentUnionSpace FlatCochainSpace CurrentLonePairImageUP
  CurrentLonePairFlatUP CurrentCompactSmoothDivergenceKernel
  FlatCochainPairFunctional FlatCochainRepresentationUP
  CurrentWeakExteriorPairUP WeakExteriorPairGraphAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CochainWeakEquation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Variable Q : Hom P W.
Hypothesis hQ : @is_current_lone_pair_flat_map R h2 n m U hU Q.

(** Source for [flat_cochain_form_density_weak_equation]:
    every pair of forms giving the two
    original alpha actions satisfies Federer's weak
    equation, 4.1.19, p. 377.
    Representation is the only form premise;
    normality, pointwise differentiability and finite
    measure of U are not required. *)
Theorem flat_cochain_form_density_weak_equation (alpha : A)
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  @is_flat_cochain_pair_density R h2 n m U hU Q alpha phi psi ->
  @is_weak_current_exterior_pair R h2 n m U hU phi psi.
Proof.
move=> hDensity.
apply: (@weak_exterior_pair_graph_action_iff R h2 n m U hU
  (@flat_cochain_pair_functional R h2 n m U hU Q alpha) phi psi hDensity).2.
move=> v hV.
exact: (@flat_cochain_pair_functional_kernel R h2 n m U hU Q hQ alpha v
  (@current_compact_smooth_divergence_pair_kernel R h2 n m U hU v hV)).
Qed.
End CochainWeakEquation.
