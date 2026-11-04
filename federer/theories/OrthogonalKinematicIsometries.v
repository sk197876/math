(** Federer (1969), 3.2.48, p. 285: the conjugations
    in the differential diagram are actual Hilbert Hom
    isometries. This is 1.7.9, p. 35, applied
    to the original orthogonal source and target operators. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductUP InnerNorm OrthogonalMaps HomInner HomOrthogonalChange
  GammaNaturality EuclideanHomInnerCharts EuclideanHomCompositionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [orthogonal_kinematic_sandwich_pairing]: the
    left and right arrows of the differential diagram preserve
    the actual Hilbert pairing, 3.2.48, p. 285,
    by the source/target invariance of 1.7.9, p. 35. *)
Lemma orthogonal_kinematic_sandwich_pairing (R:realType) N
    (s t f g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear s) ->
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear t) ->
  euclidean_hom_inner_product (hom_comp t (hom_comp f s)) (hom_comp t (hom_comp g s))=
    euclidean_hom_inner_product f g.
Proof.
move=>hs ht.
have hSandwich (L:Hom (R_n R N) (R_n R N)):
    hom_comp t (hom_comp L s)=Hom_sandwich (hom_as_linear s) (hom_as_linear t) L.
  by apply:hom_ext=>z.
rewrite !hSandwich.
exact (@hom_inner_orthogonal_change R (R_n R N) (R_n R N)
  (@euclidean_inner_product R N) (@euclidean_inner_product R N)
  (@euclidean_inner_productP R N) (@euclidean_inner_productP R N)
  N (@coordinate_basis R N) (@coordinate_basisP R N)
  (hom_as_linear s) (hom_as_linear t) hs ht f g).
Qed.

(** Source for [orthogonal_kinematic_sandwich_norm]: the conjugated
    subtraction in 3.2.48, p. 285, has the same
    actual norm before and after the orthogonal sandwich.
    Empty coordinate blocks and singular middle maps remain. *)
Lemma orthogonal_kinematic_sandwich_norm (R:realType) N
    (s t f:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear s) ->
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear t) ->
  inner_norm (@euclidean_hom_inner_productP R N N) (hom_comp t (hom_comp f s))=
    inner_norm (@euclidean_hom_inner_productP R N N) f.
Proof.
move=>hs ht; apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr.
exact (esym (@orthogonal_kinematic_sandwich_pairing R N s t f f hs ht)).
Qed.
