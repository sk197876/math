(** Federer (1969), 3.3.4, p. 288: retain the extreme
    plane dimensions before the positive-dimensional averaging proof.
    These facts follow from the original Grassmann basis laws and
    actual orthogonal-frame existence, with frames kept local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct FiniteCoordinates OrthogonalMaps OrthogonalFinite
  GrassmannHomogeneousSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_plane_member]: the zero
    plane endpoint supporting Federer 3.3.4, p. 288.
    Every member of an actual zero-dimensional Grassmann
    plane is zero; its orthogonal frame is chosen locally. *)
Lemma structure_zero_plane_member (R:realType) n (V:G (R_n R n) 0) x:
  grassmann_val V x ->x=0.
Proof.
move=>hx.
have [f [hf hImage]]:=@grassmann_orthogonal_frame R (R_n R 0) (R_n R n)
  (@euclidean_inner_product R 0) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R 0) (@euclidean_inner_productP R n)
  0 (@coordinate_basis R 0) (@coordinate_basisP R 0) V.
have [u hu]:=(hImage x).1 hx.
have hu0:u=0 by apply/ffunP=>i; have hi:=ltn_ord i; rewrite ltn0 in hi.
by rewrite -hu hu0 linear0.
Qed.

(** Source for [structure_full_plane_member]: the full
    plane endpoint supporting Federer 3.3.4, p. 288.
    Every original Euclidean vector belongs to an actual
    n-dimensional Grassmann plane in R^n. *)
Lemma structure_full_plane_member (R:realType) n (V:G (R_n R n) n) x:
  grassmann_val V x.
Proof.
have [f [hf hImage]]:=@grassmann_orthogonal_frame R (R_n R n) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) V.
have [u hu]:=@orthogonal_endomorphism_surjective R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) f hf x.
apply/(hImage x); by exists u.
Qed.
