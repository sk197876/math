(** Federer (1969), 4.1.25, p. 383: outside
    f(spt xi), every original defined term is zero,
    hence the original vector fibre sum is zero.
    This exact statement precedes any almost-everywhere
    modification of the target density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorMaps PartialFunctionUP CurrentAreaNormalisedImageUP
  CurrentAreaNormalisedImageSealed CurrentAreaFibreSumUP CurrentAreaFibreSumZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_fibre_outside_support]:
    the zero density off the original support image,
    implicit in Federer 4.1.25, p. 383. No
    input point is discarded from a fibre, and
    neither injectivity nor a nonempty support is assumed. *)
Theorem current_area_fibre_outside_support (R : realType)
    (h2 : (1+1 : R) != 0) m n
    (f : R_n R m -> R_n R n)
    (xi : R_n R m -> exterior_power (R_n R m) m)
    (K : set (R_n R m)) y eta :
  (forall x, ~K x -> xi x = 0) -> ~(f @` K) y ->
  @is_current_area_fibre_sum R (R_n R m) n m f
    (@CurrentAreaNormalisedImage.value R m n f xi) y eta -> eta = 0.
Proof.
move=> hOff hOutside hSum.
apply: (@current_area_fibre_sum_zero R h2 (R_n R m) n m f _ y eta hSum).
move=> x v hXY hValue.
have hNotK : ~K x.
  move=> hx; apply: hOutside; by exists x.
have [D [_ [_ hFormula]]] :=
  (@CurrentAreaNormalisedImage.laws R m n f xi x v).1 hValue.
by rewrite -hFormula /current_area_normalised_image_coefficient
  (hOff x hNotK) linear0 scaler0.
Qed.
