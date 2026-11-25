(** Federer (1969), 4.1.19, p. 377:
    both forms representing the same original
    pair functional are almost unique. Each
    original Omega factor is tested separately,
    and the preceding scalar uniqueness is reused. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingPairing CurrentDomain CurrentCoefficientNorms MeasureAlmostUP
  EuclideanOpenDomainMeasure CurrentLonePairImageUP
  CompactSummableMultivectors FlatCochainRepresentationUP
  CompactMultivectorFormUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PairAlmostUniqueness.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).

(** Source for [lone_pair_form_density_almost_unique]:
    the almost uniqueness assertion of Federer
    4.1.19, p. 377, for both
    representing degrees on the literal original U.
    The fields need not have the same
    pointwise bounds and need not be pointwise equal. *)
Theorem lone_pair_form_density_almost_unique (beta : Hom P R^o)
    (phi phi' : UT -> A_m X R^o m)
    (psi psi' : UT -> A_m X R^o m.+1) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  @is_lone_pair_form_density R h2 n m U hU beta phi' psi' ->
  measure_almost_everywhere mu [set x | phi x=phi' x] /\
  measure_almost_everywhere mu [set x | psi x=psi' x].
Proof.
move=> [hPhi [hPsi [hLeft hRight]]] [hPhi' [hPsi' [hLeft' hRight']]].
split.
- apply: (@compact_multivector_form_density_almost_unique R h2 n m U hU
    phi phi' hPhi.1 hPhi'.1)=> xi.
  exists (beta (xi,0)); split; first exact: hLeft.
  exact: hLeft'.
- apply: (@compact_multivector_form_density_almost_unique R h2 n m.+1 U hU
    psi psi' hPsi.1 hPsi'.1)=> eta.
  exists (beta (0,eta)); split; first exact: hRight.
  exact: hRight'.
Qed.
End PairAlmostUniqueness.
