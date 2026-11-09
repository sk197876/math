(** Federer (1969), 3.3.4, p. 290:
    active-space projection is the actual adjoint
    of its orthogonal inclusion. These laws
    follow from 1.7.4, p. 30, for
    rectangular maps, including zero dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws Bilinear OrthogonalMaps AdjointCriteria
  EuclideanRectangularAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_orthogonal_injection_adjoint_cancel]:
    q restricted to the active space is
    its inverse inclusion, supporting X and q
    in Federer 3.3.4, p. 290, directly
    by the adjoint characterization 1.7.4, p. 30. *)
Lemma euclidean_orthogonal_injection_adjoint_cancel (R:realType) d n
    (w:Hom (R_n R d) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R d)
    (@euclidean_inner_product R n) (hom_as_linear w) ->
  cancel w (euclidean_rectangular_adjoint w).
Proof.
move=>hW; exact:((orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R d)
  (euclidean_rectangular_adjoint_pairing w)).1 hW).
Qed.

(** Source for [euclidean_orthogonal_injection_normal_pairing]:
    the complement of the actual active
    space is exactly the kernel of its
    projection, supporting X and q in Federer
    3.3.4, p. 290. Every projected residual
    is orthogonal to every original active vector. *)
Lemma euclidean_orthogonal_injection_normal_pairing (R:realType) d n
    (w:Hom (R_n R d) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R d)
    (@euclidean_inner_product R n) (hom_as_linear w) ->forall u x,
    euclidean_inner_product (w u) (x-w (euclidean_rectangular_adjoint w x))=0.
Proof.
move=>hW u x.
rewrite (bilBr (inner_bilinear (@euclidean_inner_productP R n))).
rewrite -euclidean_rectangular_adjoint_pairing hW.
by rewrite subrr.
Qed.
