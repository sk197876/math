(** Federer (1969), 3.2.46, printed pp. 281--282: independent
    graph specification of the actual function sqrt(discr(g)).
    The domain is exactly the original coordinate domain A. The
    Hausdorff-measure density formula is a separate theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations RealMetricBackground
  PartialFunctionUP RiemannianTensorUP PositiveNormFactorDiscriminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_riemannian_volume_density]: the actual function
    (discr g)^(1/2) in Federer 3.2.46, pp. 281--282. The local
    proof of positivity specifies the actual discriminant; undefined
    points outside A remain outside the graph. *)
Definition is_riemannian_volume_density (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (j : partial_function (R_n R n) (real_line_metric R)) :=
  forall x z, partial_function_graph j x z <->
    exists hx : A x,
      z = Num.sqrt (euclidean_inner_form_discriminant (riemannian_tensor_inner hg hx)).
