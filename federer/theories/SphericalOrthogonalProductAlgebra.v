(** Federer (1969), 3.2.47, p. 282: exact algebra
    of the actual product chart (Phi,H_e) and its inverse.
    Section values and orthogonality are proved separately and then
    discharged at the application, not assumed as a bundle theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_isotropy]: the actual
    fibre I=Phi^-1{c} in 3.2.47, p. 282,
    as a subset of the original Hilbert Hom space. *)
Definition spherical_orthogonal_isotropy (R:realType) n (c:R_n R n):=
  [set h:Hom (R_n R n) (R_n R n)|
    is_orthogonal_map (@euclidean_inner_product R n)
      (@euclidean_inner_product R n) (hom_as_linear h) /\h c=c].

(** Source for [spherical_section_product_coordinate]: the printed
    H_e(g)=F(Phi(e^-1 g))^-1 e^-1 g in
    3.2.47, p. 282, with actual orthogonal inverses
    represented by the already sealed adjoint. *)
Definition spherical_section_product_coordinate (R:realType) n
    (e f g:Hom (R_n R n) (R_n R n)):=
  hom_comp (euclidean_rectangular_adjoint f)
    (hom_comp (euclidean_rectangular_adjoint e) g).

(** Source for [spherical_section_product_inverse]: the actual
    inverse (a,h) to e F(e^-1 a)h of the
    product chart in 3.2.47, p. 282. The
    section value is supplied here by its exact pointwise law. *)
Definition spherical_section_product_inverse (R:realType) n
    (e f h:Hom (R_n R n) (R_n R n)):=hom_comp e (hom_comp f h).

(** Source for [spherical_section_product_coordinate_member]: the
    actual H_e(g) fixes c and is orthogonal, hence
    lies in the printed isotropy I, 3.2.47, p. 282. *)
Theorem spherical_section_product_coordinate_member (R:realType) n (c:R_n R n)
    (e f g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear e) ->
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear f) ->
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear g) ->
  f c=euclidean_rectangular_adjoint e (g c) ->
  spherical_orthogonal_isotropy c (spherical_section_product_coordinate e f g).
Proof.
move=>he hf hg hValue; split.
- move=>x y; change (euclidean_inner_product
    (euclidean_rectangular_adjoint f (euclidean_rectangular_adjoint e (g x)))
    (euclidean_rectangular_adjoint f (euclidean_rectangular_adjoint e (g y)))=
    euclidean_inner_product x y).
  by rewrite (euclidean_orthogonal_adjoint_orthogonal hf)
    (euclidean_orthogonal_adjoint_orthogonal he) hg.
- change (euclidean_rectangular_adjoint f (euclidean_rectangular_adjoint e (g c))=c).
  rewrite -hValue; exact (@euclidean_orthogonal_adjoint_cancel R n f hf c).
Qed.

(** Source for [spherical_section_product_left_inverse]: the
    inverse chart recovers each original g, as claimed by
    the diffeomorphism in 3.2.47, p. 282. *)
Theorem spherical_section_product_left_inverse (R:realType) n
    (e f g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear e) ->
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear f) ->
  spherical_section_product_inverse e f (spherical_section_product_coordinate e f g)=g.
Proof.
move=>he hf; apply:hom_ext=>x.
change (e (f (euclidean_rectangular_adjoint f (euclidean_rectangular_adjoint e (g x))))=g x).
by rewrite (euclidean_orthogonal_adjoint_cancel_reverse hf)
  (euclidean_orthogonal_adjoint_cancel_reverse he).
Qed.

(** Source for [spherical_section_product_right_inverse]: H_e
    recovers the original h coordinate after the inverse map,
    supporting the exact diffeomorphism in 3.2.47, p. 282. *)
Theorem spherical_section_product_right_inverse (R:realType) n
    (e f h:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear e) ->
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear f) ->
  spherical_section_product_coordinate e f (spherical_section_product_inverse e f h)=h.
Proof.
move=>he hf; apply:hom_ext=>x.
change (euclidean_rectangular_adjoint f (euclidean_rectangular_adjoint e (e (f (h x))))=h x).
by rewrite (euclidean_orthogonal_adjoint_cancel he) (euclidean_orthogonal_adjoint_cancel hf).
Qed.

(** Source for [spherical_section_product_base_value]: the inverse
    chart has its original first coordinate a whenever its
    second coordinate lies in I, 3.2.47, p. 282. *)
Theorem spherical_section_product_base_value (R:realType) n (c a:R_n R n)
    (e f h:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear e) ->
  f c=euclidean_rectangular_adjoint e a ->spherical_orthogonal_isotropy c h ->
  spherical_section_product_inverse e f h c=a.
Proof.
move=>he hValue [_ hh].
change (e (f (h c))=a); rewrite hh hValue.
exact (@euclidean_orthogonal_adjoint_cancel_reverse R n e he a).
Qed.
