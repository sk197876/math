(** Federer (1969), 3.2.28(1), printed p. 263: the
    independent coordinate functionals on Y_m, supporting
    its finite basis and exact dimension. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanSymmetricEndomorphismSpace EuclideanSymmetricCoordinates
  EuclideanSymmetricUpperCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Functionals.
Variable R:realType.
Variable m:nat.
Local Notation E:=(Hom (R_n R m) (R_n R m)).
Local Notation S:=(@euclidean_symmetric_hom_subspace R m).
Local Notation Y:=(subspace_space S).
Local Notation I:=(euclidean_symmetric_indices m).

(** Source for [euclidean_symmetric_upper_coordinate_fun]: the
    independent i<=j coefficient of an actual symmetric
    endomorphism, supporting Federer 3.2.28(1), p. 263. *)
Definition euclidean_symmetric_upper_coordinate_fun (a:I) (y:Y):R^o:=
  euclidean_hom_coefficient (subspace_val y) (val a).1 (val a).2.

(** Source for [euclidean_symmetric_upper_coordinate_linear]:
    linearity of the independent coefficient functionals,
    supporting the dimension count of 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_upper_coordinate_linear a:
  linear (euclidean_symmetric_upper_coordinate_fun a).
Proof.
move=>c x y; rewrite /euclidean_symmetric_upper_coordinate_fun
  (linearP (@subspace_val R E S)).
exact:(@euclidean_hom_coefficient_linear R m m (val a).1 (val a).2
  c (subspace_val x) (subspace_val y)).
Qed.
HB.instance Definition _ a:=GRing.isLinear.Build R Y R^o *:%R
  (euclidean_symmetric_upper_coordinate_fun a)
  (euclidean_symmetric_upper_coordinate_linear a).

(** Source for [euclidean_symmetric_upper_coordinate]: the
    linear independent-coordinate functional on Y_m,
    supporting Federer 3.2.28(1), p. 263. *)
Definition euclidean_symmetric_upper_coordinate (a:I):Hom Y R^o:=
  hom_of_linear (GRing.Linear.clone _ _ _ _
    (euclidean_symmetric_upper_coordinate_fun a) _).

(** Source for [euclidean_symmetric_upper_coordinates_injective]:
    a symmetric endomorphism is determined by its entries
    with i<=j, supporting dim Y_m=m(m+1)/2
    in Federer 3.2.28(1), p. 263. *)
Theorem euclidean_symmetric_upper_coordinates_injective (u v:Y):
  (forall a:I,euclidean_symmetric_upper_coordinate a u=
    euclidean_symmetric_upper_coordinate a v) ->u=v.
Proof.
move=>hEq; apply:subspace_val_injective; apply:hom_ext.
apply:(basis_linear_ext (@coordinate_basisP R m)
  (hom_as_linear (subspace_val u)) (hom_as_linear (subspace_val v)))=>j.
apply/ffunP=>i.
change (euclidean_hom_coefficient (subspace_val u) i j=
  euclidean_hom_coefficient (subspace_val v) i j).
case:(leqP i j)=>hij.
- pose a:I:=Sub (i,j) hij.
  exact:(hEq a).
- have hji:(j<=i)%N:=ltnW hij.
  pose a:I:=Sub (j,i) hji.
  have hU:=(@euclidean_symmetric_hom_coordinateP R m (subspace_val u)).1
    (@subspace_valP R E S u) i j.
  have hV:=(@euclidean_symmetric_hom_coordinateP R m (subspace_val v)).1
    (@subspace_valP R E S v) i j.
  rewrite hU hV; exact:(hEq a).
Qed.
End Functionals.
Arguments euclidean_symmetric_upper_coordinate {R m} a.
