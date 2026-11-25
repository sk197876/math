(** Federer (1969), 4.1.23, p. 380:
    the equal-degree identification in R times S
    transports its literal constant density by the
    same exterior-degree identification. This is only
    the original equality of natural indices. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading ExteriorHomogeneousProducts
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentCharacteristicDensity EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_characteristic_degree_transport]:
    the actual characteristic-density current retains
    its original measurable set when the
    two equal degrees are identified,
    supporting Federer 4.1.23, p. 380.
    Neither a quotient representative nor a
    different current topology is introduced. *)
Theorem current_characteristic_degree_transport (R : realType)
    (h2 : (1+1:R)!=0) n p q (e : p=q)
    (A : set (R_n R n))
    (hA : measure_measurable (@euclidean_lebesgue_measure R n) A)
    (z : exterior_power (R_n R n) p) :
  let Full := fun _ : R_n R n => True in
  let hFull := fun (x : R_n R n) (_ : True) => norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) x in
  let cell := fun k B hB w => @current_characteristic_density R h2 n k
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) B hB w in
  @current_degree_transport R h2 n Full hFull p q e (cell p A hA z)=
    cell q A hA (exterior_reindex e z).
Proof.
case: q /e; move=> Full hFull cell.
by rewrite current_degree_transport_identity.
Qed.
