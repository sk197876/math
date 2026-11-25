(** Federer (1969), 3.1.15, p. 227: the kth differential
    of a map on R^m is recovered from its multi-partials
    D^alpha f(a) through fixed bounded linear maps, by the
    coordinate expansion of 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP NormDifferentialUP NormHigherDifferentialUP
  NormHigherMultiPartialUP NormHigherCoordinateReconstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Reconstruction.
Variable R : realType.
Variable m : nat.
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable k : nat.

(** Source for [higher_differential_actual_multi_partial]:
    the evaluation of an actual kth differential on the
    coordinate vectors e^alpha is the multi-partial
    D^alpha f(a), Federer 3.1.11, p. 223, as used in
    3.1.15, p. 227. *)
Lemma higher_differential_actual_multi_partial (A : X->Prop) (f : X->Y) (a : X) (z : Z k)
    (alpha : symmetric_indices m k) :
  has_norm_higher_differential NX ev ZN A f k a z ->
  has_norm_multi_partial NX ev ZN A f alpha a (@ev k (norm_multi_partial_arguments R alpha) z).
Proof. by move=>hz; exists z. Qed.

(** Source for [higher_differential_coordinate_reconstruction]:
    the kth differential of a map on R^m is recovered from
    its multi-partials D^alpha f(a) by the coordinate expansion
    of Federer 3.1.11, p. 223, as used in 3.1.15, p. 227:
    z = sum_alpha iota_alpha (ev(e^alpha) z) with fixed bounded
    linear maps iota_alpha : Y -> Z_k. *)
Theorem higher_differential_coordinate_reconstruction :
  exists iota : symmetric_indices m k->Hom Y (Z k),
    (forall alpha, norm_bounded_linear NY (@ZN k) (iota alpha)) /\
    forall (A : X->Prop) (f : X->Y) (a : X) (z : Z k),
      has_norm_higher_differential NX ev ZN A f k a z ->
      z=\sum_alpha iota alpha (@ev k (norm_multi_partial_arguments R alpha) z).
Proof.
have [iota [hb he]] := @norm_higher_coordinate_reconstruction_exists R m Y NY hNY Z ev ZN hZ k.
exists iota; split; first exact hb.
move=>A f a z hz.
exact: (he A f a z (fun alpha=>@ev k (norm_multi_partial_arguments R alpha) z) hz
  (fun alpha=>higher_differential_actual_multi_partial alpha hz)).
Qed.
End Reconstruction.
