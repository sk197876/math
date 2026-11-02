(** Public angular B function for Federer (1969), 3.2.13,
    pp. 250–251, evaluated only on its positive-coordinate domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EulerBetaUP EulerBetaSealed GaussianProductIntegrand HausdorffMeasure PartialFunctionUP
  MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_beta]: evaluation of the angular B
    function on a positive coordinate family, Federer 3.2.13,
    p. 250, without assigning outside-domain values. *)
Definition euler_beta (R:realType) m (hm:(0<m)%N) (z:R_n R m) (hz:forall j,0<z j):R:=
  projT1 (cid (euler_beta_domain_law (@EulerBeta.laws R m hm) hz)).

(** Source for [euler_beta_value_graph]: the evaluated angular
    value belongs to the opaque B graph, Federer 3.2.13, p. 250. *)
Lemma euler_beta_value_graph (R:realType) m (hm:(0<m)%N) (z:R_n R m) (hz:forall j,0<z j):
  partial_function_graph (@EulerBeta.value R m hm) z (euler_beta hm hz).
Proof. exact:projT2 (cid (euler_beta_domain_law (@EulerBeta.laws R m hm) hz)). Qed.

(** Source for [euler_beta_positive]: positivity of B at its
    positive coordinate parameters, Federer 3.2.13, pp. 250–251. *)
Lemma euler_beta_positive (R:realType) m (hm:(0<m)%N) (z:R_n R m) (hz:forall j,0<z j):
  0<euler_beta hm hz.
Proof. exact:(euler_beta_positive_law (@EulerBeta.laws R m hm) (euler_beta_value_graph hm hz)). Qed.

(** Source for [euler_beta_integral]: the defining equation
    2B(z)=the actual sphere integral of the coordinate powers,
    Federer 3.2.13, p. 250. *)
Lemma euler_beta_integral (R:realType) m (hm:(0<m)%N) (z:R_n R m) (hz:forall j,0<z j):
  is_measure_subset_integral
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set u|inner_norm (@euclidean_inner_productP R m) u= 1]
    (real_total_integrand (gaussian_angular_integrand z)) (2*euler_beta hm hz)%:E.
Proof. exact:((euler_beta_graph_law (@EulerBeta.laws R m hm) z _).1 (euler_beta_value_graph hm hz)).2. Qed.
