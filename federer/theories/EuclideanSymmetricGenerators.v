(** Federer (1969), 3.2.28(1), printed p. 263: symmetric
    coordinate generators supporting dim Y_m=m(m+1)/2.
    Only this finite-dimensional existence proof uses coordinates. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom TensorUP ModuleQuotient GrassmannAbbreviations
  FiniteCoordinates EuclideanSymmetricCoordinates EuclideanSymmetricEndomorphismSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Generators.
Variable R:realType.
Variable m:nat.
Local Notation X:=(R_n R m).

(** Source for [euclidean_symmetric_generator_fun]: the
    diagonal coordinate map or symmetric off-diagonal pair,
    supporting the dimension count of Federer 3.2.28(1),
    p. 263. The off-diagonal generator has entries one
    in both transposed positions; the diagonal has only one. *)
Definition euclidean_symmetric_generator_fun (i j:'I_m) (x:X):X:=
  x j*:(@coordinate_basis R m i)+
    (if i==j then 0 else x i*:(@coordinate_basis R m j)).

(** Source for [euclidean_symmetric_generator_linear]:
    linearity of the symmetric coordinate generators used in
    Federer 3.2.28(1), p. 263, by the elementary
    coordinate linearity of 1.4.5, p. 21. *)
Lemma euclidean_symmetric_generator_linear i j:
  linear (euclidean_symmetric_generator_fun i j).
Proof.
move=>c x y.
have hCoordinate k:(c*:x+y) k=c*x k+y k by rewrite !ffunE.
rewrite /euclidean_symmetric_generator_fun !hCoordinate.
case:(i==j); first by rewrite !addr0 scalerDl scalerA.
by rewrite !scalerDl scalerDr !scalerA addrACA.
Qed.
HB.instance Definition _ i j:=GRing.isLinear.Build R X X *:%R
  (euclidean_symmetric_generator_fun i j)
  (euclidean_symmetric_generator_linear i j).

(** Source for [euclidean_symmetric_generator]: the actual
    endomorphism underlying a symmetric coordinate generator,
    supporting Federer 3.2.28(1), p. 263. *)
Definition euclidean_symmetric_generator (i j:'I_m):Hom X X:=
  hom_of_linear (GRing.Linear.clone _ _ _ _ (euclidean_symmetric_generator_fun i j) _).

(** Source for [euclidean_symmetric_generator_coefficient]:
    the precise two coordinate entries of a symmetric
    generator, supporting dim Y_m in Federer 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_generator_coefficient (i j r s:'I_m):
  euclidean_hom_coefficient (euclidean_symmetric_generator i j) r s=
    (if s==j then 1 else 0)*(if r==i then 1 else 0)+
    (if i==j then 0 else (if s==i then 1 else 0)*(if r==j then 1 else 0)).
Proof.
rewrite /euclidean_hom_coefficient /euclidean_symmetric_generator hom_of_linearE.
change (euclidean_symmetric_generator_fun i j (@coordinate_basis R m s) r=
  (if s==j then 1 else 0)*(if r==i then 1 else 0)+
  (if i==j then 0 else (if s==i then 1 else 0)*(if r==j then 1 else 0))).
rewrite /euclidean_symmetric_generator_fun /coordinate_basis.
case:(i==j); rewrite !ffunE (eq_sym j s) ?(eq_sym i s); reflexivity.
Qed.

(** Source for [euclidean_symmetric_generator_membership]:
    each coordinate generator really belongs to Y_m,
    supporting Federer 3.2.28(1), p. 263. *)
Lemma euclidean_symmetric_generator_membership i j:
  euclidean_symmetric_hom_subspace (euclidean_symmetric_generator i j).
Proof.
apply:(@euclidean_symmetric_hom_coordinateP R m
  (euclidean_symmetric_generator i j)).2=>r s.
rewrite !euclidean_symmetric_generator_coefficient.
case:(eqVneq i j)=>[->|hij].
- by ring.
- by rewrite ?(negbTE hij); ring.
Qed.
End Generators.
