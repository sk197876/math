(** Federer (1969), 3.2.28(1), printed p. 263: coordinate
    support for dim Y_m=m(m+1)/2. Coordinates are used
    only to prove the finite basis assertion, not to replace
    the abstract symmetric-endomorphism definition. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient LinearBasis GrassmannAbbreviations
  FiniteCoordinates CoordinateProjection EuclideanInnerProduct InnerProductUP
  InnerProductLaws EuclideanRectangularAdjoint EuclideanSymmetricEndomorphismSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hom_coefficient]: the i,j coefficient
    relative to the standard bases, supporting the dimension
    calculation in Federer 3.2.28(1), p. 263; basis
    coefficients are introduced in 1.4.5, p. 21. *)
Definition euclidean_hom_coefficient (R:realType) m n
    (f:Hom (R_n R m) (R_n R n)) (i:'I_n) (j:'I_m):R:=
  f (@coordinate_basis R m j) i.

(** Source for [euclidean_hom_coefficient_linear]: coefficients
    depend linearly on the map, 1.4.5, p. 21, supporting
    the finite basis calculation of 3.2.28(1), p. 263. *)
Lemma euclidean_hom_coefficient_linear (R:realType) m n (i:'I_n) (j:'I_m):
  linear (fun f:Hom (R_n R m) (R_n R n)=>
    (euclidean_hom_coefficient f i j:R^o)).
Proof.
move=>c f g; rewrite /euclidean_hom_coefficient hom_addE hom_scaleE.
by rewrite !ffunE.
Qed.

(** Source for [euclidean_adjoint_coefficient]: the adjoint
    interchanges the two coefficient indices, 1.7.4, p. 30,
    supporting Y_m in Federer 3.2.28(1), p. 263. *)
Lemma euclidean_adjoint_coefficient (R:realType) m n
    (f:Hom (R_n R m) (R_n R n)) (i:'I_m) (j:'I_n):
  euclidean_hom_coefficient (euclidean_rectangular_adjoint f) i j=
    euclidean_hom_coefficient f j i.
Proof.
rewrite /euclidean_hom_coefficient
  -(euclidean_inner_basis (euclidean_rectangular_adjoint f (@coordinate_basis R n j)) i)
  (inner_symmetric (@euclidean_inner_productP R m))
  euclidean_rectangular_adjoint_pairing euclidean_inner_basis; reflexivity.
Qed.

(** Source for [euclidean_symmetric_hom_coordinateP]: Y_m
    consists exactly of the symmetric coefficient arrays,
    supporting dim Y_m=m(m+1)/2 in Federer
    3.2.28(1), p. 263. All natural m are included. *)
Theorem euclidean_symmetric_hom_coordinateP (R:realType) m
    (f:Hom (R_n R m) (R_n R m)):
  euclidean_symmetric_hom_subspace f <->
    forall i j,euclidean_hom_coefficient f i j=euclidean_hom_coefficient f j i.
Proof.
split.
- move=>hf i j; change (euclidean_rectangular_adjoint f=f) in hf.
  by rewrite -euclidean_adjoint_coefficient hf.
- move=>hf; change (euclidean_rectangular_adjoint f=f).
  apply:hom_ext.
  apply:(basis_linear_ext (@coordinate_basisP R m)
    (hom_as_linear (euclidean_rectangular_adjoint f)) (hom_as_linear f))=>j.
  apply/ffunP=>i.
  change (euclidean_hom_coefficient (euclidean_rectangular_adjoint f) i j=
    euclidean_hom_coefficient f i j).
  rewrite euclidean_adjoint_coefficient; exact:hf.
Qed.
