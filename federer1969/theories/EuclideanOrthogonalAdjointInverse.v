(** Federer (1969), 3.2.47, pp. 282–283: the
    inverse orthogonal operators in the actual local product chart
    are their adjoints. These supporting algebraic laws retain
    dimension zero and use only public adjoint and orthogonality laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  OrthogonalMaps AdjointCriteria EuclideanRectangularAdjoint EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_orthogonal_adjoint_cancel]: the actual
    identity g* g=identity from 1.7.4, p. 30,
    supporting the inverse operators of 3.2.47, p. 282. *)
Lemma euclidean_orthogonal_adjoint_cancel (R:realType) n
    (g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  cancel g (euclidean_rectangular_adjoint g).
Proof.
move=>hg; exact ((orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R n)
  (euclidean_rectangular_adjoint_pairing g)).1 hg).
Qed.

(** Source for [euclidean_orthogonal_adjoint_cancel_reverse]: the
    actual identity g g*=identity for square orthogonal
    operators, supporting 3.2.47, p. 282. Surjectivity
    is derived from finite dimension and orthogonal injectivity. *)
Lemma euclidean_orthogonal_adjoint_cancel_reverse (R:realType) n
    (g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  cancel (euclidean_rectangular_adjoint g) g.
Proof.
move=>hg x.
have hInjective:injective (hom_as_linear g).
  exact (@orthogonal_map_injective R (R_n R n) (R_n R n)
    _ _ (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
    (hom_as_linear g) hg).
have [y hy]:=@euclidean_injective_surjective R n (hom_as_linear g) hInjective x.
change (g y=x) in hy; rewrite -hy.
by rewrite (euclidean_orthogonal_adjoint_cancel hg).
Qed.

(** Source for [euclidean_orthogonal_adjoint_orthogonal]: the inverse
    appearing in H_e is itself orthogonal, supporting the
    exact local product chart of 3.2.47, p. 282. *)
Lemma euclidean_orthogonal_adjoint_orthogonal (R:realType) n
    (g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  is_orthogonal_map (@euclidean_inner_product R n)
    (@euclidean_inner_product R n) (hom_as_linear (euclidean_rectangular_adjoint g)).
Proof.
move=>hg.
exact (@orthogonal_inverse R (R_n R n) (R_n R n) _ _ (hom_as_linear g)
  (hom_as_linear (euclidean_rectangular_adjoint g)) hg
  (@euclidean_orthogonal_adjoint_cancel_reverse R n g hg)).
Qed.
