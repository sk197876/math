(** Federer (1969), 3.1.21, p. 234: tangent space
    to the local image from the constant-rank section of 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLinear
  NormDifferentialInverseIdentities NormOpenDomainLaws TangentConeUP TangentOpenDomain
  TangentEmbeddingUP TangentEmbeddingImage NormLinearLeftInverseBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_section_tangent_image]: supporting
    Tan[f(U),f(a)]=im Df(a) in Federer 3.1.21,
    p. 234. A differentiable section with a bounded
    linear left inverse has tangent equal to its derivative
    range, when that range is closed. Every inverse-continuity
    and homogeneous lower-bound premise is derived here. *)
Theorem norm_section_tangent_image (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (psi:X->Y) a (L:Hom X Y) (p:Hom Y X) :
  has_norm_differential NX NY A psi a L -> norm_bounded_linear NY NX p ->
  (forall x,A x -> p (psi x)=x) ->
  @closed (real_norm_metric_space hNY) (range L) ->
  norm_tangent_cone NY (psi @` A) (psi a)=range L.
Proof.
move=>hpsi hp hcan hclosed.
have ha:=norm_domain_interior_member hNX (norm_differential_interior hpsi).
have hpd:=@norm_differential_linear R Y X NY NX hNY hNX setT (psi a) p
  (norm_full_domain_interior NY (psi a)) hp.
have hlin:=@norm_differentials_left_inverse R X Y NX NY hNX hNY A setT psi p a L p
  (fun _ _=>I) hcan hpsi hpd.
have hleft:cancel L p.
  move=>v; exact (congr1 (fun H:Hom X X=>H v) hlin).
have hlower:=@norm_linear_left_inverse_lower_bound R X Y NX NY hNY L p hp hleft.
have hinv:norm_inverse_continuous_on_set NX NY A psi a.
  move=>e he; have [C [hC hb]]:=hp.
  have hCp:0<C+1 by lra.
  have hd:0<e/(C+1) by rewrite divr_gt0.
  exists (e/(C+1)); split=>// x hx hsmall.
  have hh:=hb (psi x-psi a).
  rewrite linearB /= (hcan x hx) (hcan a ha) in hh.
  have hn:=real_seminorm_nonnegative hNY.1 (psi x-psi a).
  have hmul:(C+1)*NY (psi x-psi a)<e.
    move: hsmall; by rewrite ltr_pdivlMr // mulrC.
  lra.
have he:=@norm_tangent_embedding_image R X Y NX NY hNX hNY A A psi a L hpsi hlower hclosed hinv.
rewrite (norm_tangent_open_domain hNX (norm_differential_interior hpsi)) in he.
exact: esym he.
Qed.
