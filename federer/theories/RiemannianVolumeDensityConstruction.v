(** Private existence of the independent discriminant-density graph,
    Federer (1969), 3.2.46, pp. 281--282. Its single-valuedness is
    proved from the intrinsic representative, without a new axiom. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations RealMetricBackground
  PartialFunctionUP RiemannianTensorUP PositiveNormFactorDiscriminant
  EuclideanFormDiscriminantProofs RiemannianVolumeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [riemannian_volume_density_exists]: existence of
    the actual function sqrt(discr(g)) on A, Federer 3.2.46,
    pp. 281--282. This is a graph witness only; no measure identity
    or derivative field is part of the existence specification. *)
Theorem riemannian_volume_density_exists (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  exists j, is_riemannian_volume_density hg j.
Proof.
have hSingle x z w :
    (exists hx : A x, z = Num.sqrt (euclidean_inner_form_discriminant
      (riemannian_tensor_inner hg hx))) ->
    (exists hx : A x, w = Num.sqrt (euclidean_inner_form_discriminant
      (riemannian_tensor_inner hg hx))) -> z = w.
  move=> [hx ->] [hy ->].
  by rewrite (euclidean_inner_form_discriminant_proof_independent
    (riemannian_tensor_inner hg hx) (riemannian_tensor_inner hg hy)).
exists (@Build_partial_function (R_n R n) (real_line_metric R)
  (fun x z => exists hx : A x, z = Num.sqrt (euclidean_inner_form_discriminant
    (riemannian_tensor_inner hg hx))) hSingle).
by move=> x z.
Qed.
