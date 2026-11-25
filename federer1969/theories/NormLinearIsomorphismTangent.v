(** Federer (1969), 3.2.28(1), printed p. 263:
    tangent cones under invertible linear ambient coordinates,
    by the tangent-image theorem of 3.1.21, p. 234. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormOpenDomainLaws NormRegularity NormRegularityOperations NormDiffeomorphismUP
  TangentConeUP NormDiffeomorphismTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_linear_isomorphism_tangent_image]: exact
    tangent transport under the ambient linear coordinates
    in Federer 3.2.28(1), p. 263, by 3.1.21,
    p. 234. Actual tangent cones and arbitrary source
    subsets are retained, without a manifold premise. *)
Theorem norm_linear_isomorphism_tangent_image (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (e:Hom X Y) (p:Hom Y X) (B:set X) b:
  norm_bounded_linear NX NY e ->norm_bounded_linear NY NX p ->
  cancel e p ->cancel p e ->
  e @` norm_tangent_cone NX B b=norm_tangent_cone NY (e @` B) (e b).
Proof.
move=>hE hP hEP hPE.
have hOpenX x (hx:setT x):norm_domain_interior NX setT x.
  exact:norm_full_domain_interior.
have hOpenY y (hy:setT y):norm_domain_interior NY setT y.
  exact:norm_full_domain_interior.
have hDiff:is_norm_diffeomorphism hNX hNY setT setT e p 1%N.
  constructor.
  - exists e,p; split=>//; split=>//; by split.
  - exact:(@norm_class_linear R X Y NX NY hNX hNY setT e 1%N hOpenX hE).
  - exact:(@norm_class_linear R Y X NY NX hNY hNX setT p 1%N hOpenY hP).
  - by move=>x hx.
  - by move=>y hy.
  - move=>x hx; exact:hEP.
  - move=>y hy; exact:hPE.
have hDerivative:=@norm_differential_linear R X Y NX NY hNX hNY setT b e
  (hOpenX b I) hE.
have hT:=@norm_diffeomorphism_tangent_image R X Y NX NY hNX hNY
  setT B setT e p 1%N b e (leqnn 1) hDiff I hDerivative.
by rewrite setIT in hT.
Qed.
