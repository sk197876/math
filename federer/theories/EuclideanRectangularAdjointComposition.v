(** Federer (1969), 1.7.4, p. 30:
    adjoints reverse composition, supporting
    the actual active projection and
    inverse-frame identities in 3.3.4,
    pp. 290–291. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  AdjointLaws EuclideanRectangularAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_rectangular_adjoint_composition]:
    (g composed with f)* equals f*
    composed with g*, Federer 1.7.4,
    p. 30, supporting q and the
    actual frame inverses in 3.3.4,
    pp. 290–291. Only the sealed
    adjoint pairing and uniqueness are used. *)
Theorem euclidean_rectangular_adjoint_composition (R:realType) a b c
    (f:Hom (R_n R a) (R_n R b)) (g:Hom (R_n R b) (R_n R c)):
  euclidean_rectangular_adjoint (hom_comp g f)=
    hom_comp (euclidean_rectangular_adjoint f) (euclidean_rectangular_adjoint g).
Proof.
apply:hom_ext=>y; apply:(inner_vectors_ext (@euclidean_inner_productP R a))=>x.
by rewrite euclidean_rectangular_adjoint_pairing !hom_compE
  !euclidean_rectangular_adjoint_pairing.
Qed.
