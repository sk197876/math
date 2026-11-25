(** Federer (1969), 4.1.25, p. 383, first display:
    the scalar integrand pairs Lambda_k Df(x)(xi(x)) with
    phi(f(x)). Its domain is exactly the original partial
    differential domain of 3.1.1, pp. 209–211. No auxiliary
    total differential supplies values outside that domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferential InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric ExteriorGrading ExteriorMaps
  AlternatingForms AlternatingPairing PartialFunctionUP
  PartialFunctionSourcePostcomposition ExtendedRealOrderTopology
  EuclideanLebesgueDimensions MeasureAlmostUP MeasureAlmostBasic
  LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueActionIntegrand.
Variable R : realType.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Variables (f : X -> Y) (xi : X -> exterior_power X k)
  (phi : Y -> A_m Y R^o k).
Local Notation DF := (norm_differential hNX hNY Full f).

(** Source for [current_lipschitz_lebesgue_action_integrand]:
    the literal first displayed integrand of 4.1.25,
    p. 383; the general exterior degree only exposes the
    natural expression used in its limiting proof. *)
Definition current_lipschitz_lebesgue_action_integrand :
    partial_function X (extended_real_line R) :=
  partial_function_source_postcompose DF
    (fun x D => (pairing
      (exterior_power_map (hom_as_linear D) k (xi x)) (phi (f x)))%:E).

(** Source for [current_lipschitz_lebesgue_action_integrand_graph]:
    each integrand value uses an actual differential of f
    at that same point, as in 4.1.25, p. 383. *)
Theorem current_lipschitz_lebesgue_action_integrand_graph x z :
  partial_function_graph current_lipschitz_lebesgue_action_integrand x z <->
  exists D : Hom X Y,
    has_norm_differential NX NY Full f x D /\
    (pairing (exterior_power_map (hom_as_linear D) k (xi x)) (phi (f x)))%:E = z.
Proof.
rewrite /current_lipschitz_lebesgue_action_integrand
  partial_function_source_postcompose_graph.
split.
- move=>[D [hD hValue]];exists D;split;last exact:hValue.
  exact:(norm_differential_graph hNX hNY Full f x D).1 hD.
- move=>[D [hD hValue]];exists D;split;last exact:hValue.
  exact:(norm_differential_graph hNX hNY Full f x D).2 hD.
Qed.

(** Source for [current_lipschitz_lebesgue_action_integrand_domain]:
    the original differential domain is preserved exactly,
    supporting the first formula of 4.1.25, p. 383,
    with the function convention of 2.3.1, p. 72. *)
Theorem current_lipschitz_lebesgue_action_integrand_domain :
  partial_function_domain current_lipschitz_lebesgue_action_integrand =
    partial_function_domain DF.
Proof.
exact: partial_function_source_postcompose_domain.
Qed.

(** Source for [current_lipschitz_lebesgue_action_integrand_defined]:
    the displayed differential expression is defined precisely
    where f is differentiable, supporting 4.1.25, p. 383. *)
Theorem current_lipschitz_lebesgue_action_integrand_defined x :
  partial_function_domain current_lipschitz_lebesgue_action_integrand x <->
    norm_differentiable_at NX NY Full f x.
Proof.
rewrite current_lipschitz_lebesgue_action_integrand_domain.
exact: norm_differential_domain.
Qed.

(** Source for [current_lipschitz_lebesgue_action_integrand_conull]:
    Rademacher supplies the full original integration domain,
    including m=0 and n=0; no differentiability premise
    is added to the Lipschitz map of 4.1.25, p. 383. *)
Theorem current_lipschitz_lebesgue_action_integrand_conull :
  @is_metric_lipschitz R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) Full f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_function_domain current_lipschitz_lebesgue_action_integrand).
Proof.
move=> hLip.
apply: (@measure_almost_everywhere_mono R X
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  _ _ _ (@federer_3_1_6 R m n f hLip))=> x hx.
exact: (current_lipschitz_lebesgue_action_integrand_defined x).2 hx.
Qed.
End LebesgueActionIntegrand.
