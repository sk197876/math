(** Federer (1969), 3.2.28, printed pp. 263–267:
    isometric ambient coordinates preserve the actual norm
    topology, as well as the metric normalization.
    Only the abstract finite-inner-chart laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm HilbertFormCompactness NormMetric NormMetricScaleContinuity
  NormLinearIsometryInverse NormDifferentialUP FiniteInnerChartUP HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_inner_chart_norm_homeomorphism]: the
    suitable Euclidean ambient identifications of Federer
    3.2.28, pp. 263–267, using 1.7.1, p. 28.
    Both inverse maps are continuous by their proved
    distance equality. *)
Theorem finite_inner_chart_norm_homeomorphism (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->
  is_homeomorphism_with_inverse
    (fun x:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))=>
      (e x:real_norm_metric_space (inner_norm_real_norm hB)))
    (fun y:real_norm_metric_space (inner_norm_real_norm hB)=>
      (p y:real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))).
Proof.
move=>h; constructor.
- apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=>x y.
  change (is_true (inner_norm hB (e x-e y)<=1*inner_norm (@euclidean_inner_productP R n) (x-y))).
  by rewrite -linearB /= (finite_inner_chart_norm hB h) mul1r.
- apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=>x y.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (p x-p y)<=1*inner_norm hB (x-y))).
  by rewrite -linearB /= (finite_inner_chart_inverse_norm hB h) mul1r.
- exact:finite_inner_chart_left_inverse h.
- exact:finite_inner_chart_right_inverse h.
Qed.
