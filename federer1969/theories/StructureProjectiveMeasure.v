(** Federer (1969), 3.3.4, pp. 290–291: the
    reference measure on the actual compact projective
    image T(U). Restrict its metric carrier before
    any finite-measure or differentiation argument;
    ambient lower-degree Hausdorff measure need not
    be finite on bounded sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  SymmetricGrading InnerSymmetricPositivity StructureProjectiveSphere
  StructureProjectiveMassBounds StructureProjectiveSpace MetricSubsetBackground
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffMetricSubset
  MeasureUP MeasureBasic BorelRegularMeasureUP MeasureDerivationContext.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_projective_measure]: H^m
    on the actual metric carrier T(U), Federer
    3.3.4, pp. 290–291. The existing sealed
    Hausdorff object supplies its independently specified
    measure; no density or Haar law is assumed. *)
Definition structure_projective_measure (R:realType) m:=
  @hausdorff_measure R (structure_projective_space R m) m.

(** Source for [structure_projective_measure_totalE]:
    intrinsic and restricted ambient H^m give
    the same actual total mass, supporting
    Federer 3.3.4, p. 290, by 2.10.11,
    p. 176, and the inherited metric. *)
Lemma structure_projective_measure_totalE (R:realType) m:
  @structure_projective_measure R m setT=
  @hausdorff_measure R
    (inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
      (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2))
    m (@structure_projective_sphere R m).
Proof.
rewrite /structure_projective_measure -hausdorff_metric_subset_measure.
congr (hausdorff_measure m _); apply/seteqP; split=>x.
- move=>[z _ <-]; exact:set_valP.
- move=>hx; exists (Sub x (mem_set hx):structure_projective_space R m); by [].
Qed.

(** Source for [structure_projective_measure_positive_finite]:
    the positive finite reference mass in Federer
    3.3.4, pp. 290–291, holds for the actual
    carrier measure, including its degree-zero atom. *)
Lemma structure_projective_measure_positive_finite (R:realType) m:
  0<@structure_projective_measure R m setT< +oo.
Proof. by rewrite structure_projective_measure_totalE; exact:structure_projective_sphere_positive_finite. Qed.

(** Source for [structure_projective_derivation_measure]:
    the actual projective reference belongs to
    the class M of 2.9.1, p. 152, used
    in Federer 3.3.4, p. 291. Its finite
    total mass gives bounded-set finiteness; the
    actual Hausdorff measure is Borel regular. *)
Theorem structure_projective_derivation_measure (R:realType) m:
  is_derivation_measure (@structure_projective_measure R m).
Proof.
constructor.
- exact:hausdorff_measure_is_measure.
- exact:hausdorff_measure_borel_regular.
- move=>A _.
  have hFinite:structure_projective_measure setT< +oo:=
    (andP (@structure_projective_measure_positive_finite R m)).2.
  apply:le_lt_trans _ hFinite.
  apply:(measure_mono (@hausdorff_measure_is_measure R (structure_projective_space R m) m)).
  by move=>x _.
Qed.
