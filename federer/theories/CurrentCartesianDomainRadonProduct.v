(** Federer (1969), 4.1.8, p. 361: the original
    product of the two variation Radon measures is
    Radon on the actual open factor domains. All
    countable bases and compact-neighbourhood covers are
    discharged by the earlier original Euclidean results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CurrentDomain CurrentDomainCountableBase
  MetricSubsetBackground MetricProductBackground SmoothDomainCompactOpenCover
  MeasureUP ProductMeasure RadonMeasureUP CountableMetricRadonProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CurrentCartesianDomainRadonProduct.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AT := [the metricType R of (metric_subset (A:set (real_norm_metric_space hNX)))].
Local Notation BT := [the metricType R of (metric_subset (B:set (real_norm_metric_space hNY)))].
Local Notation P := [the metricType R of (metric_product AT BT)].

(** Source for [current_domain_radon_product]: the original
    Cartesian product of Radon measures on the two
    original open domains is Radon, supporting the
    integration formula in Federer 4.1.8, p. 361.
    No global or bounded-set finiteness premise is added. *)
Theorem current_domain_radon_product
    (alpha:set (current_domain R m A)->\bar R)
    (beta:set (current_domain R n B)->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta):
  is_radon_measure alpha->is_radon_measure beta->
    @is_radon_measure R P (product_measure hAlpha hBeta).
Proof.
move=>hRA hRB.
have[B1 hB1]:=@current_domain_countable_open_base R m A.
have[B2 hB2]:=@current_domain_countable_open_base R n B.
have[C1 [W1 [hC1 [hW1 [hWC1 [hCoverC1 hCoverW1]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX m (@coordinate_basis R m) (@coordinate_basisP R m) A hA.
have[C2 [W2 [hC2 [hW2 [hWC2 [hCoverC2 hCoverW2]]]]]]:=
  @smooth_domain_compact_open_cover R Y NY hNY n (@coordinate_basis R n) (@coordinate_basisP R n) B hB.
exact:(@countable_metric_radon_product R AT BT alpha beta hAlpha hBeta hRA hRB
  B1 B2 hB1 hB2 C1 W1 C2 W2 hC1 hC2 hW1 hW2 hWC1 hWC2 hCoverW1 hCoverW2).
Qed.
End CurrentCartesianDomainRadonProduct.
