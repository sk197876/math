(** Federer (1969), 3.2.20, p. 256: well-definedness and
    exact domain of the intrinsic approximate Jacobian. The supporting
    proofs use the approximate differential's graph laws and the
    independently specified partial exterior norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness PartialFunctionUP MeasureUP
  MeasureApproximateDifferentialUP MeasureApproximateDifferential
  MeasureApproximateDifferentialUniqueness MeasureApproximateLinearModel
  PartialExteriorNormUP PartialExteriorNormLaws PartialExteriorNorm
  MeasureApproximateJacobianUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [measure_approximate_jacobian_unique]: well-definedness
    of the value ap J_m f in Federer 3.2.20, p. 256.
    The actual partial approximate differential is unique, and the least
    exterior-word bound is unique. No ambient representative is used
    in this uniqueness statement. *)
Lemma measure_approximate_jacobian_unique (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) a J L :
  has_measure_approximate_jacobian phi m q f a J ->
  has_measure_approximate_jacobian phi m q f a L -> J=L.
Proof.
move=> [d [hd hJ]] [e [he hL]].
have hEq := measure_approximate_differential_unique hd he.
rewrite -hEq in hL; exact: partial_exterior_norm_unique hJ hL.
Qed.

(** Source for [measure_approximate_jacobian_value_exists]: the norm
    exists whenever f has an actual approximate differential, as required
    in Federer 3.2.20, p. 256. An ambient differential bounds
    the actual word costs; it does not define the norm by arbitrary
    off-tangent values. Degree q is arbitrary, including zero. *)
Theorem measure_approximate_jacobian_value_exists (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) a :
  is_measure phi ->
  measure_approximately_differentiable_at (inner_norm (@euclidean_inner_productP R k))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) phi m f a ->
  exists J : R, has_measure_approximate_jacobian phi m q f a J.
Proof.
move=> hm ha.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose NY := inner_norm (@euclidean_inner_productP R k).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R k).
pose d := @measure_approximate_differential R (R_n R n) (R_n R k) NX NY hNX hNY phi m hm f a ha.
have hd : is_measure_approximate_differential NY hNX phi m f a d.
  split; first exact ha.
  exact: (@measure_approximate_differential_graph R (R_n R n) (R_n R k) NX NY hNX hNY
    phi m hm f a ha).
have [D [_ hModel]] := @measure_approximate_differential_linear_model R
  (R_n R n) (R_n R k) NX NY hNX hNY phi m f a d hm hd.
have [J hJ] := partial_exterior_norm_linear_model_exists q hModel.
exists J,d; by split.
Qed.

(** Source for [measure_approximate_jacobian_domain_iff]: the word
    "whenever" in the definition of the approximate Jacobian in Federer
    3.2.20, p. 256. The graph's domain is exactly actual
    approximate differentiability, with no default value elsewhere, also
    in exterior degree zero. *)
Lemma measure_approximate_jacobian_domain_iff (R : realType) n k
    (phi : set (R_n R n) -> \bar R) m q
    (f : partial_function (R_n R n) (R_n R k)) a :
  is_measure phi ->
  ((exists J, has_measure_approximate_jacobian phi m q f a J) <->
    measure_approximately_differentiable_at (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) phi m f a).
Proof.
move=> hm; split.
- by move=> [J [d [hd _]]]; exact hd.1.
- exact: (@measure_approximate_jacobian_value_exists R n k phi m q f a hm).
Qed.
