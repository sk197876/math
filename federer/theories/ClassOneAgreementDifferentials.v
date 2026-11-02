(** Federer (1969), 3.2.31, pp. 268–269: supporting
    transfer of actual differential ranks to closed class-one
    agreement pieces, by the density-one uniqueness used in
    3.2.10, p. 248. No derivative is assigned by a default. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  ClassOneAgreementCoverUP NormDifferentialUP EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  DensityDifferentialAgreement MeasureAlmostUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [class_one_agreement_cover_differentials]: supporting
    the derivative-rank decomposition in Federer 3.2.31, p. 269.
    Actual differentials of the original map and each class-one
    representative agree almost everywhere on their closed
    equality set. Closed-set measurability and the existing
    density theorem discharge the agreement assertion. *)
Theorem class_one_agreement_cover_differentials (R:realType) m n
    (F:R_n R m.+1->R_n R n) G C:
  @is_class_one_agreement_cover R m n F G C ->forall j,
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) (C j)
    [set a|forall D E:Hom (R_n R m.+1) (R_n R n),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m.+1))
        (inner_norm (@euclidean_inner_productP R n)) setT F a D ->
      has_norm_differential (inner_norm (@euclidean_inner_productP R m.+1))
        (inner_norm (@euclidean_inner_productP R n)) setT (G j) a E ->D=E].
Proof.
move=>hCover j.
exact (@measurable_set_differential_agreement_almost R m.+1 (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  F (G j) (C j) (euclidean_borel_measurable (closed_borel_set (@class_one_agreement_cover_closed R m n F G C hCover j)))
  (@class_one_agreement_cover_equal R m n F G C hCover j)).
Qed.
