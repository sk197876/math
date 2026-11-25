(** Public Hausdorff measure for the actual original
    curve distance, Federer (1969), 3.2.46, p. 281.
    The finite-carrier formula is a proved representation,
    not its defining axiom or a private implementation appeal. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorffUP
  RiemannianHausdorffCompatibility RiemannianHausdorffSealed RealHausdorffMeasure
  MeasureUP BorelRegularMeasureUP CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [riemannian_hausdorff_measure]: actual Gamma-
    normalized original-rho Hausdorff measure in every real
    degree p>=0, Federer 3.2.46, p. 281. *)
Definition riemannian_hausdorff_measure (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :=
  @RiemannianHausdorff.value R n A g hg p hp.
Arguments riemannian_hausdorff_measure {R n A g} hg p hp.

(** Source for [riemannian_hausdorff_measure_laws]: the public
    original-rho measure satisfies the independent covering
    specification, supporting 3.2.46, p. 281. *)
Lemma riemannian_hausdorff_measure_laws (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :
  is_riemannian_hausdorff_measure hg p hp (riemannian_hausdorff_measure hg p hp).
Proof. exact: RiemannianHausdorff.laws. Qed.

(** Source for [riemannian_hausdorff_carrier]: exact
    representation by the finite metric carrier follows from
    the proved original cutoff/cost compatibility, supporting
    3.2.46, p. 281. No volume formula is used. *)
Lemma riemannian_hausdorff_carrier (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) B :
  riemannian_hausdorff_measure hg p hp B =
    @real_hausdorff_measure R [the metricType R of riemannian_metric_space hg] p hp B.
Proof.
exact: (riemannian_hausdorff_measure_unique
  (@riemannian_hausdorff_measure_laws R n A g hg p hp)
  (@riemannian_hausdorff_carrier_laws R n A g hg p hp)).
Qed.

(** Source for [riemannian_hausdorff_is_measure]: original-rho
    Hausdorff measure has all outer-measure laws, supporting
    Federer 3.2.46, p. 281. *)
Lemma riemannian_hausdorff_is_measure (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :
  is_measure (riemannian_hausdorff_measure hg p hp).
Proof.
have hEq : riemannian_hausdorff_measure hg p hp =
    @real_hausdorff_measure R [the metricType R of riemannian_metric_space hg] p hp.
  apply: funext=> B; exact: riemannian_hausdorff_carrier.
rewrite hEq; exact: real_hausdorff_measure_is_measure.
Qed.

(** Source for [riemannian_hausdorff_borel_regular]: Borel
    regularity of original-rho Hausdorff measure, supporting
    3.2.46, p. 281. Topology compatibility is separately proved. *)
Lemma riemannian_hausdorff_borel_regular (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :
  is_borel_regular_measure (riemannian_hausdorff_measure hg p hp).
Proof.
have hEq : riemannian_hausdorff_measure hg p hp =
    @real_hausdorff_measure R [the metricType R of riemannian_metric_space hg] p hp.
  apply: funext=> B; exact: riemannian_hausdorff_carrier.
rewrite hEq; exact: real_hausdorff_measure_borel_regular.
Qed.

(** Source for [riemannian_hausdorff_zero_counting]: actual
    degree-zero measure is counting, retaining the positive
    zero-dimensional atom in 3.2.46, p. 281; see 2.10.2, p. 171. *)
Lemma riemannian_hausdorff_zero_counting (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (hp : (0<=0 :> R)) B :
  riemannian_hausdorff_measure hg 0 hp B =
    @counting_measure R [the choiceType of riemannian_metric_space hg] B.
Proof. rewrite riemannian_hausdorff_carrier; exact: real_hausdorff_zero_counting. Qed.
