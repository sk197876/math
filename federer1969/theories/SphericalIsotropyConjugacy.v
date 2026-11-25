(** Federer (1969), 3.2.47, pp. 282–283: change
    the chosen pole by an actual orthogonal conjugacy. The
    conjugacy preserves the original Frobenius metric, fixes
    no global frame, and has an explicit two-sided inverse. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm OrthogonalMaps HomInner HomOrthogonalChange GammaNaturality
  EuclideanHomInnerCharts EuclideanHomCompositionBound EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse SphericalOrthogonalProductAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_isotropy_conjugate]: actual orthogonal
    conjugation Q h Q^-1 identifies the isotropies at
    p and Q(p), supporting 3.2.47, p. 282. *)
Definition spherical_isotropy_conjugate (R:realType) n
    (Q h:Hom (R_n R n) (R_n R n)):=
  Hom_sandwich (hom_as_linear (euclidean_rectangular_adjoint Q)) (hom_as_linear Q) h.

(** Source for [spherical_isotropy_unconjugate]: actual inverse
    conjugation Q^-1 H Q, supporting the isotropy
    identification of 3.2.47, p. 282. *)
Definition spherical_isotropy_unconjugate (R:realType) n
    (Q H:Hom (R_n R n) (R_n R n)):=
  Hom_sandwich (hom_as_linear Q) (hom_as_linear (euclidean_rectangular_adjoint Q)) H.

(** Source for [spherical_isotropy_conjugacy_cancel]: inverse
    conjugation recovers every original operator, supporting
    the exact isomorphism in 3.2.47, p. 282. *)
Lemma spherical_isotropy_conjugacy_cancel (R:realType) n
    (Q:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear Q) ->
  cancel (spherical_isotropy_conjugate Q) (spherical_isotropy_unconjugate Q).
Proof.
move=>hQ h; apply:hom_ext=>x.
change (euclidean_rectangular_adjoint Q (Q (h (euclidean_rectangular_adjoint Q (Q x))))=h x).
by rewrite !(euclidean_orthogonal_adjoint_cancel hQ).
Qed.

(** Source for [spherical_isotropy_conjugacy_cancel_reverse]: forward
    conjugation recovers every original operator after inverse
    conjugation, supporting 3.2.47, p. 282. *)
Lemma spherical_isotropy_conjugacy_cancel_reverse (R:realType) n
    (Q:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear Q) ->
  cancel (spherical_isotropy_unconjugate Q) (spherical_isotropy_conjugate Q).
Proof.
move=>hQ h; apply:hom_ext=>x.
change (Q (euclidean_rectangular_adjoint Q (h (Q (euclidean_rectangular_adjoint Q x))))=h x).
by rewrite !(euclidean_orthogonal_adjoint_cancel_reverse hQ).
Qed.

(** Source for [spherical_isotropy_conjugacy_member]: conjugation
    takes the original isotropy at p onto the original
    isotropy at Q(p), supporting 3.2.47, p. 282. *)
Lemma spherical_isotropy_conjugacy_member (R:realType) n (p:R_n R n)
    (Q h:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear Q) ->
  spherical_orthogonal_isotropy p h ->
  spherical_orthogonal_isotropy (Q p) (spherical_isotropy_conjugate Q h).
Proof.
move=>hQ [hh hFixed]; split.
- move=>x y; change (euclidean_inner_product
    (Q (h (euclidean_rectangular_adjoint Q x)))
    (Q (h (euclidean_rectangular_adjoint Q y)))=euclidean_inner_product x y).
  by rewrite hQ hh (euclidean_orthogonal_adjoint_orthogonal hQ).
- change (Q (h (euclidean_rectangular_adjoint Q (Q p)))=Q p).
  by rewrite (euclidean_orthogonal_adjoint_cancel hQ) hFixed.
Qed.

(** Source for [spherical_isotropy_unconjugacy_member]: the
    inverse conjugation returns every actual isotropy element,
    supporting surjectivity of the isomorphism in 3.2.47, p. 282. *)
Lemma spherical_isotropy_unconjugacy_member (R:realType) n (p:R_n R n)
    (Q H:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear Q) ->
  spherical_orthogonal_isotropy (Q p) H ->
  spherical_orthogonal_isotropy p (spherical_isotropy_unconjugate Q H).
Proof.
move=>hQ [hH hFixed]; split.
- move=>x y; change (euclidean_inner_product
    (euclidean_rectangular_adjoint Q (H (Q x)))
    (euclidean_rectangular_adjoint Q (H (Q y)))=euclidean_inner_product x y).
  by rewrite (euclidean_orthogonal_adjoint_orthogonal hQ) hH hQ.
- change (euclidean_rectangular_adjoint Q (H (Q p))=p).
  rewrite hFixed; exact (@euclidean_orthogonal_adjoint_cancel R n Q hQ p).
Qed.

(** Source for [spherical_isotropy_conjugacy_distance]: the isotropy
    conjugacy preserves the actual Hilbert Hom distances,
    as needed for I isometric with O(n-1),
    3.2.47, pp. 282–283; use 1.7.9,
    p. 35, rather than only a topological identification. *)
Theorem spherical_isotropy_conjugacy_distance (R:realType) n
    (Q h g:Hom (R_n R n) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) (hom_as_linear Q) ->
  inner_norm (@euclidean_hom_inner_productP R n n)
    (spherical_isotropy_conjugate Q h-spherical_isotropy_conjugate Q g)=
  inner_norm (@euclidean_hom_inner_productP R n n) (h-g).
Proof.
move=>hQ.
have hDifference:spherical_isotropy_conjugate Q h-spherical_isotropy_conjugate Q g=
    spherical_isotropy_conjugate Q (h-g).
  exact (esym (@linB R (Hom (R_n R n) (R_n R n)) (Hom (R_n R n) (R_n R n))
    (Hom_sandwich (hom_as_linear (euclidean_rectangular_adjoint Q)) (hom_as_linear Q))
    (Hom_sandwich_linear _ _) h g)).
rewrite hDifference !euclidean_hilbert_hom_normE.
exact (@hom_norm_orthogonal_change R (R_n R n) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n)
  (hom_as_linear (euclidean_rectangular_adjoint Q)) (hom_as_linear Q)
  (@euclidean_orthogonal_adjoint_orthogonal R n Q hQ) hQ (h-g)).
Qed.
