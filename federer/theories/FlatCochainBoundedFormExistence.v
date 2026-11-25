(** Federer (1969), 4.1.19, p. 377: apply
    the original first cost bound to the
    functional induced by alpha, then represent
    its two Omega components on the same U. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CurrentSpaces SmoothCompactSet CurrentFlatNorm FlatCurrentsUP
  FlatCurrentUnionSpace FlatCochainSpace CurrentLonePairImageUP
  CurrentLonePairCost FlatCochainPairFunctional FlatCochainRepresentationUP
  BoundedPairFormRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CochainForms.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation UT := (current_domain R n U).
Local Notation X := (R_n R n).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation N := (@flat_cochain_norm R h2 n m U hU).
Variable Q : Hom P W.
Hypothesis hFirst : forall v : P,
  exists K : smooth_compact_set hNX U,
    flatK K (inc (Q v)) /\ fine (FK K (inc (Q v))) <= J v.

(** Source for [flat_cochain_pair_functional_bound]:
    beta has the original bound F(alpha) J
    in Federer 4.1.19, p. 377.
    This supporting adapter consumes precisely the
    first cost conclusion of 4.1.18, p. 375,
    rather than a norm on the whole flat union. *)
Theorem flat_cochain_pair_functional_bound (alpha : A) :
  forall v, `|@flat_cochain_pair_functional R h2 n m U hU Q alpha v|
    <= N alpha*J v.
Proof.
move=> v.
have hNorm := @flat_cochain_norm_laws R h2 n m U hU alpha.
have [K [hFlat hCost]] := @hFirst v.
rewrite flat_cochain_pair_functional_evaluation.
exact: (le_trans (hNorm.1.2 K (Q v) hFlat)
  (ler_wpM2l hNorm.1.1 hCost)).
Qed.

(** Source for [flat_cochain_bounded_form_density_exists]:
    the bounded measurable forms representing alpha
    in Federer 4.1.19, p. 377,
    exist on its original U and both
    have pointwise comass at most F(alpha).
    The weak equation and exact norm identity
    are separate conclusions proved from the representation. *)
Theorem flat_cochain_bounded_form_density_exists (alpha : A) :
  exists phi : UT -> A_m X R^o m,
  exists psi : UT -> A_m X R^o m.+1,
    @is_flat_cochain_pair_density R h2 n m U hU Q alpha phi psi /\
    (forall x, @current_form_comass R h2 n m (phi x) <= N alpha) /\
    forall x, @current_form_comass R h2 n m.+1 (psi x) <= N alpha.
Proof.
have hNorm := @flat_cochain_norm_laws R h2 n m U hU alpha.
exact: (@bounded_lone_pair_form_representation R h2 n m U hU
  (@flat_cochain_pair_functional R h2 n m U hU Q alpha)
  (N alpha) hNorm.1.1 (flat_cochain_pair_functional_bound alpha)).
Qed.
End CochainForms.
