(** Federer (1969), 3.2.46, pp. 281–282: the total
    view of the existing sealed density graph on its actual
    chart domain. This is its exact value sqrt(discr g(x)),
    not a newly chosen frame or an auxiliary field. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartReference RiemannianVolumeDensity RiemannianVolumeDensityContinuity
  PositiveNormFactorDiscriminant EuclideanDiscriminantPolynomial PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_chart_volume_density]: the exact
    value of the original density graph at each chart member,
    supporting 3.2.46, pp. 281–282. Membership proofs change
    neither the discriminant nor this value. *)
Definition riemannian_chart_volume_density (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (x : riemannian_metric_space hg) : real_line_metric R :=
  Num.sqrt (euclidean_inner_form_discriminant (riemannian_tensor_inner hg (set_valP x))).
Arguments riemannian_chart_volume_density {R n A g} hg x.

(** Source for [riemannian_chart_volume_density_graph]: this
    chart view has exactly the value required by the sealed
    original-domain density graph, 3.2.46, pp. 281–282. *)
Lemma riemannian_chart_volume_density_graph (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x :
  partial_function_graph (riemannian_volume_density hg) (val x)
    (riemannian_chart_volume_density hg x).
Proof.
apply/(riemannian_volume_density_laws hg); exists (set_valP x); by [].
Qed.

(** Source for [riemannian_chart_volume_density_positive]:
    every actual chart value is strictly positive, including
    degree zero, supporting 3.2.46, pp. 281–282. *)
Lemma riemannian_chart_volume_density_positive (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x :
  0<riemannian_chart_volume_density hg x.
Proof. rewrite /riemannian_chart_volume_density sqrtr_gt0; exact: euclidean_inner_discriminant_positive. Qed.

(** Source for [riemannian_chart_volume_density_continuous]:
    the actual density is continuous in the proved rho
    topology, supporting 3.2.46, pp. 281–282. *)
Lemma riemannian_chart_volume_density_continuous (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  continuous (riemannian_chart_volume_density hg).
Proof.
exact (@riemannian_volume_density_along_continuous_map R n A g hg
  [the topologicalType of riemannian_metric_space hg]
  (fun x=>val x) (fun x=>set_valP x)
  (@riemannian_chart_inclusion_continuous R n A g hg)).
Qed.
