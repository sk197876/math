(** Opaque curve-infimum interface, Federer (1969), 3.2.46, p. 281.
    The private order construction proves existence only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianDistanceUP RiemannianDistanceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.

Module Type RiemannianDistanceSignature.
(** Source for [value]: the actual curve infimum rho(x,y),
    Federer 3.2.46, p. 281, specified solely by its public laws. *)
Parameter value : forall (R : realType) n
  (A : set (inner_metric_space (@euclidean_inner_productP R n)))
  (g : R_n R n -> R_n R n -> R_n R n -> R), R_n R n -> R_n R n -> \bar R.
(** Source for [laws]: greatest-lower-bound laws of the actual
    curve distance, Federer 3.2.46, p. 281. *)
Parameter laws : forall (R : realType) n A g x y,
  @is_riemannian_curve_distance R n A g x y (@value R n A g x y).
End RiemannianDistanceSignature.

Module RiemannianDistance : RiemannianDistanceSignature.
(** Source for [value]: opaque selection from proved existence
    of the infimum, Federer 3.2.46, p. 281. *)
Definition value (R : realType) n A g x y :=
  projT1 (cid (@riemannian_curve_distance_exists R n A g x y)).
(** Source for [laws]: the selected infimum satisfies the
    independent laws, Federer 3.2.46, p. 281. *)
Lemma laws (R : realType) n A g x y :
  @is_riemannian_curve_distance R n A g x y (@value R n A g x y).
Proof. exact: projT2 (cid (@riemannian_curve_distance_exists R n A g x y)). Qed.
End RiemannianDistance.
