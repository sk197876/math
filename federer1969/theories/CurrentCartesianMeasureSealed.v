(** Federer (1969), 4.1.8, p. 361: the original
    product measure on the actual Euclidean product domain.
    Keep the coordinate and all-set laws public and the
    existence construction opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanCartesianMap CurrentDomain
  MeasureUP CurrentCartesianMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CartesianCurrentMeasureSignature.
(** Source for [value]: the original product measure on
    the actual product domain, supporting Federer 4.1.8,
    p. 361, through 2.6.5, pp. 119–120. *)
Parameter value:forall (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (alpha:set (current_domain R m A)->\bar R)
    (beta:set (current_domain R n B)->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta),
  set (current_domain R (m+n) (@euclidean_cartesian_set R m n A B))->\bar R.
(** Source for [laws]: the independent original all-set
    product-measure specification, supporting Federer 4.1.8,
    p. 361. *)
Parameter laws:forall (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (alpha:set (current_domain R m A)->\bar R)
    (beta:set (current_domain R n B)->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta),
  @is_current_cartesian_measure R m n A B alpha beta hAlpha hBeta
    (@value R m n A B alpha beta hAlpha hBeta).
End CartesianCurrentMeasureSignature.
Module CartesianCurrentMeasure:CartesianCurrentMeasureSignature.
(** Source for [value]: seal the proved original measure
    witness, supporting Federer 4.1.8, p. 361. *)
Definition value (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (alpha:set (current_domain R m A)->\bar R)
    (beta:set (current_domain R n B)->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta):
  set (current_domain R (m+n) (@euclidean_cartesian_set R m n A B))->\bar R:=
  projT1 (cid (@current_cartesian_measure_exists R m n A B alpha beta hAlpha hBeta)).
(** Source for [laws]: the opaque original product satisfies
    its independent coordinate and measure laws, supporting
    Federer 4.1.8, p. 361. *)
Lemma laws (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (alpha:set (current_domain R m A)->\bar R)
    (beta:set (current_domain R n B)->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta):
  @is_current_cartesian_measure R m n A B alpha beta hAlpha hBeta
    (@value R m n A B alpha beta hAlpha hBeta).
Proof. exact:(projT2 (cid (@current_cartesian_measure_exists R m n A B alpha beta hAlpha hBeta))). Qed.
End CartesianCurrentMeasure.
