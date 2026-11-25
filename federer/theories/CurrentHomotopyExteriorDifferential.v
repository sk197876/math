(** Federer (1969), 4.1.9, p. 363: the exterior image
    of the original time-space vector is h-dot_t wedged with
    the exterior spatial differential. This is the algebraic
    identity used both in the form integral and the represented
    current orientation formula, before any almost-everywhere choice. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts ExteriorNormNaturality
  ExteriorDegreeOneNorm ExteriorMapScaling CurrentCartesianVectorProduct CurrentMapDifferential
  CurrentHomotopyUP CurrentHomotopyTimeVelocity CurrentHomotopySliceDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyExteriorDifferential.
Variable R:realType.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hClass:@is_current_homotopy_class R n nu A U V f g h 1%N.
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Local Notation DH t x := (@current_map_differential R (1+n)%N nu AU h (Point t x)).
Local Notation DS t x := (@current_map_differential R n nu U (@current_homotopy_slice_map R n nu h t) x).
Local Notation Velocity t x := (@current_homotopy_time_velocity R n nu A U h t x).
Local Notation u := (@euclidean_one_embed R 0).
Local Notation v := (@euclidean_one_embed R 1).
Local Notation TimeVector := (exterior_first_inclusion (R_n R 1%N) (v-u)).
Local Notation Product := (@current_cartesian_vector_product R 1%N n 1%N j).
Local Notation Q := (@euclidean_last_injection_map R 1%N n).

(** Source for [current_homotopy_exterior_differential]: the
    original exterior time-space image is exactly
    h-dot_t(x) wedge Lambda_j Dh_t(x) eta, supporting both
    displayed orientation and differential-form assertions in
    Federer 4.1.9, p. 363. The equation holds at
    every original domain point for every multivector eta. *)
Theorem current_homotopy_exterior_differential t x (eta:exterior_power X j):
  A t->U x->
  exterior_power_map (hom_as_linear (DH t x)) (1+j) (Product TimeVector eta)=
    exterior_product (exterior_first_inclusion Y (Velocity t x))
      (exterior_power_map (hom_as_linear (DS t x)) j eta).
Proof.
move=>ht hx.
have hUnit:v-u=@euclidean_one_embed R 1.
  apply/ffunP=>i;rewrite /euclidean_one_embed !ffunE.
  change ((1:R)-0 = 1);exact:subr0.
rewrite /current_cartesian_vector_product exterior_power_map_product !exterior_map_first_inclusion hUnit.
congr (exterior_product _ _).
rewrite exterior_power_map_composition
  (@current_homotopy_slice_differential R n nu A U V f g h hClass t x ht hx).
apply:(@exterior_power_map_ext R X Y
  (linear_comp (hom_as_linear (DH t x)) (hom_as_linear Q))
  (hom_as_linear (hom_comp (DH t x) Q)) _ j eta)=>w.
change ((DH t x) (Q w)=(hom_comp (DH t x) Q) w).
by rewrite hom_compE.
Qed.
End CurrentHomotopyExteriorDifferential.
