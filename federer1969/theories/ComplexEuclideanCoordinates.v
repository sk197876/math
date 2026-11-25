(** Federer (1969), 3.4.12, p. 339: the original standard
    complex coordinate space is isometric to the real space with
    twice as many coordinates. Reuse the exact inverse coordinate
    maps and inner-product identity of 1.8.2, p. 39. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed FiniteCoordinates GrassmannAbbreviations
  StandardHermitian StandardHermitianCoordinates HermitianRealImaginary InnerNorm EuclideanInnerProduct
  HolomorphicCoordinateNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Variable n:nat.
Local Notation C:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space C n).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Y:=(R_n R (n+n)).

(** Source for [complex_from_real_coordinates_linear]: the actual
    inverse coordinate identification is real linear,
    supporting 3.4.12, p. 339. *)
Lemma complex_from_real_coordinates_linear:linear (@complex_from_real_coordinates R n:Y->XR).
Proof.
move=>a u v;apply:(can_inj (@complex_real_coordinatesK R n)).
rewrite (@complex_from_real_coordinatesK R n (a*:u+v)).
rewrite (@complex_real_coordinates_linear R n a (complex_from_real_coordinates u) (complex_from_real_coordinates v)).
by rewrite !complex_from_real_coordinatesK.
Qed.

(** Source for [complex_from_real_coordinate_hom]: the original
    real-to-complex identification as a real linear map,
    3.4.12, p. 339. *)
Definition complex_from_real_coordinate_hom:Hom Y XR:=
  @HomMap R Y XR (@complex_from_real_coordinates R n)
    (introT (asboolP _) complex_from_real_coordinates_linear).

(** Source for [complex_real_coordinate_hom]: the original
    complex-to-real coordinate identification as a real linear map,
    3.4.12, p. 339. *)
Definition complex_real_coordinate_hom:Hom XR Y:=
  hom_of_linear (GRing.Linear.clone R XR Y *:%R (@complex_real_coordinates R n) _).

(** Source for [complex_euclidean_coordinate_norm]: the exact
    original norm equality in the paired real coordinates,
    3.4.12, p. 339. *)
Lemma complex_euclidean_coordinate_norm (x:X):
  @holomorphic_coordinate_norm R n x=
    inner_norm (@euclidean_inner_productP R (n+n)) (complex_real_coordinates x).
Proof.
apply:inner_norm_value;first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr.
exact:esym (@standard_hermitian_real_coordinates R n x x).
Qed.

(** Source for [complex_inverse_euclidean_coordinate_norm]: the
    inverse original chart preserves the same norm,
    3.4.12, p. 339. *)
Lemma complex_inverse_euclidean_coordinate_norm (y:Y):
  @holomorphic_coordinate_norm R n (complex_from_real_coordinates y)=
    inner_norm (@euclidean_inner_productP R (n+n)) y.
Proof. by rewrite complex_euclidean_coordinate_norm complex_from_real_coordinatesK. Qed.
End Coordinates.
