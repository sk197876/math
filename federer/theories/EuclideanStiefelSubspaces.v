(** Federer (1969), 3.2.28(2), printed p. 264:
    the actual horizontal subspace Z(g) and the Stiefel
    tangent kernel. Their predicates are the printed linear
    equations; no basis or coordinate construction defines them. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient
  GrassmannAbbreviations EuclideanRectangularAdjoint
  EuclideanGramDifferentialAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_stiefel_horizontal_subspace]:
    Z(g)={h:g* h=0}, equivalently h* g=0, in
    Federer 3.2.28(2), p. 264. This is the actual
    linear subspace, before any coordinate choice. *)
Definition euclidean_stiefel_horizontal_subspace (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
    subspace (Hom (R_n R m) (R_n R n)).
Proof.
apply:(@Subspace R (Hom (R_n R m) (R_n R n))
  (fun h=>hom_comp (euclidean_rectangular_adjoint g) h=0)).
- apply:hom_ext=>x; by rewrite hom_compE hom_zeroE linear0.
- move=>h k hh hk; apply:hom_ext=>x.
  have hH:=congr1 (fun L:Hom (R_n R m) (R_n R m)=>L x) hh.
  have hK:=congr1 (fun L:Hom (R_n R m) (R_n R m)=>L x) hk.
  change (euclidean_rectangular_adjoint g (h x)=0) in hH.
  change (euclidean_rectangular_adjoint g (k x)=0) in hK.
  rewrite hom_compE hom_addE linearD.
  change (euclidean_rectangular_adjoint g (h x)+euclidean_rectangular_adjoint g (k x)=0).
  by rewrite hH hK add0r.
- move=>c h hh; apply:hom_ext=>x.
  have hH:=congr1 (fun L:Hom (R_n R m) (R_n R m)=>L x) hh.
  change (euclidean_rectangular_adjoint g (h x)=0) in hH.
  rewrite hom_compE hom_scaleE linearZ.
  change (c*:euclidean_rectangular_adjoint g (h x)=0).
  by rewrite hH scaler0.
Defined.
Arguments euclidean_stiefel_horizontal_subspace {R m n} g.

(** Source for [euclidean_stiefel_tangent_subspace]: the
    kernel h* g+g* h=0 in Federer 3.2.28(1)–(2),
    pp. 263–264. Equality with the actual geometric tangent
    has been proved separately by the regular-level theorem. *)
Definition euclidean_stiefel_tangent_subspace (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
    subspace (Hom (R_n R m) (R_n R n)).
Proof.
apply:(@Subspace R (Hom (R_n R m) (R_n R n))
  (fun h=>euclidean_gram_differential g h=0)).
- exact:linear0.
- move=>h k hh hk; rewrite linearD.
  change (euclidean_gram_differential g h+euclidean_gram_differential g k=0).
  by rewrite hh hk add0r.
- move=>c h hh; rewrite linearZ.
  change (c*:euclidean_gram_differential g h=0).
  by rewrite hh scaler0.
Defined.
Arguments euclidean_stiefel_tangent_subspace {R m n} g.
