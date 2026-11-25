(** Federer (1969), 4.1.27, p. 384:
    for nonzero zeta the simplex density
    is zeta/|zeta| on the displayed
    image and zero elsewhere. For zero
    zeta, choose the zero representative on
    the H^m-null degenerate image. This convention
    makes no normalized-unit assertion there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorNorm EuclideanLinearMaps SimplexCubeParametrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [simplex_normalised_orientation]: zeta/|zeta| in
    4.1.27, p. 384, when |zeta|>0,
    using the original exterior norm. The
    algebraic totalisation is zero when zeta=0;
    it selects a representative on the
    H^m-null degenerate image, not a printed
    normalized unit vector. *)
Definition simplex_normalised_orientation (R:realType) n m
    (v:'I_(m.+1)->R_n R n):exterior_power (R_n R n) m:=
  (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (simplex_consecutive_orientation v))^-1*:simplex_consecutive_orientation v.

(** Source for [is_simplex_hausdorff_density]: the two exact
    original coefficient values in the final
    display of 4.1.27, p. 384.
    The field is specified independently of
    a piecewise-function witness or a current construction. *)
Record is_simplex_hausdorff_density (R:realType) n m
    (v:'I_(m.+1)->R_n R n)
    (w:R_n R n->exterior_power (R_n R n) m):Prop:={
  (** Source: eta=|zeta|^-1 zeta on f(C) for nonzero zeta,
      Federer 4.1.27, p. 384. At zeta=0 this law chooses
      the zero representative on the H^m-null image. *)
  simplex_hausdorff_density_inside:forall y,
    simplex_positive_barycentric_image v y->w y=simplex_normalised_orientation v;
  (** Source: eta=0 off f(C),
      Federer 4.1.27, p. 384. *)
  simplex_hausdorff_density_outside:forall y,
    ~simplex_positive_barycentric_image v y->w y=0
}.

(** Source for [simplex_hausdorff_density_unique]: the original
    on-image and off-image laws uniquely determine
    the field in 4.1.27, p. 384. *)
Theorem simplex_hausdorff_density_unique (R:realType) n m
    (v:'I_(m.+1)->R_n R n) (w z:R_n R n->exterior_power (R_n R n) m):
  is_simplex_hausdorff_density v w->is_simplex_hausdorff_density v z->w=z.
Proof.
move=>hW hZ;apply:funext=>y;case:(pselect (simplex_positive_barycentric_image v y))=>hY.
- by rewrite (simplex_hausdorff_density_inside hW hY) (simplex_hausdorff_density_inside hZ hY).
- by rewrite (simplex_hausdorff_density_outside hW hY) (simplex_hausdorff_density_outside hZ hY).
Qed.
