(** Federer (1969), 3.1.21, p. 234,
    used for the example cited in 3.4.10,
    p. 338: a genuine differentiable curve in
    the original set supplies its actual tangent vector. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  TangentConeUP TangentConeBasic TangentOpenDomain TangentDifferentialImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [differentiable_curve_tangent_vector]: apply the
    tangent-image inclusion of 3.1.21, p. 234,
    to the scalar direction one, retaining the curve's
    actual open domain and original set membership. *)
Theorem differentiable_curve_tangent_vector (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set R^o) (S:set X)
    (f:R^o->X) a (L:Hom R^o X):
  has_norm_differential (fun t:R^o=>`|t|) NX A f a L ->
  (forall t,A t ->S (f t)) ->norm_tangent_cone NX S (f a) (L 1).
Proof.
move=>hD hS.
have hFull:norm_tangent_cone (fun t:R^o=>`|t|) setT a 1.
  rewrite (@norm_tangent_open_domain R R^o (fun t:R^o=>`|t|)
    (@scalar_absolute_value_norm R) setT a
    (norm_full_domain_interior (fun t:R^o=>`|t|) a));done.
have hImage:=@norm_differential_tangent_image R R^o X (fun t:R^o=>`|t|) NX
  (@scalar_absolute_value_norm R) hNX A setT f a L hD 1 hFull.
apply:(@norm_tangent_mono R X NX (f @` (setT `&` A)) S (f a) _ (L 1) hImage).
by move=>x [t [_ ht] <-];exact:hS t ht.
Qed.
