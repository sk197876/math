(** Federer (1969), 1.8.2, p. 40: the equality criterion
    is an exact paired product, without an additional positive scalar.
    A nonnegative scalar can be absorbed into the first pair by
    scaling its complex vector by the real square root. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors ScalarRestriction ComplexScalarSealed
  ComplexPairedVectors PairedRealVectors PairedVectorNaturality PairedFirstScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Scaling.
Variable R : rcfType.
Variable V : lmodType (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation VR := (restricted_space embed V).
Variable k : nat.

(** Source for [paired_complex_vector_scale_first]: Federer 1.8.2,
    p. 40, scaling the first complex vector by a real t multiplies
    its real-imaginary paired product by t squared. *)
Lemma paired_complex_vector_scale_first t (v : 'I_k.+1 -> V) :
  @paired_complex_vector R V k.+1 (@scale_first_family R VR k t v) =
    t^+2 *: paired_complex_vector v.
Proof.
rewrite -!paired_real_complex_identification.
have hj : (fun j => ii *: @scale_first_family R VR k t v j) =
    @scale_first_family R VR k t (fun j => ii *: v j).
  apply: funext => j; rewrite /scale_first_family; case: ifP=> _; last by [].
  change (ii *: (embed t *: v j) = embed t *: (ii *: v j)).
  by rewrite !scalerA mulrC.
rewrite hj; exact: paired_real_vector_scale_first.
Qed.

(** Source for [nonnegative_scaled_paired_vector]: Federer 1.8.2,
    p. 40, extending the unit equality case to arbitrary lengths:
    each nonnegative multiple of a positive-degree paired product
    is itself a paired product, with no independence requirement. *)
Theorem nonnegative_scaled_paired_vector r (hr : 0 <= r) (v : 'I_k.+1 -> V) :
  exists w : 'I_k.+1 -> V, paired_complex_vector w = r *: paired_complex_vector v.
Proof.
exists (@scale_first_family R VR k (Num.sqrt r) v).
by rewrite paired_complex_vector_scale_first sqr_sqrtr.
Qed.

(** Source for [zero_paired_complex_representation]: Federer 1.8.2,
    p. 40, the zero vector satisfies the printed equality criterion
    in every positive paired degree. *)
Theorem zero_paired_complex_representation :
  exists w : 'I_k.+1 -> V, paired_complex_vector w = 0.
Proof.
have [w hw] := nonnegative_scaled_paired_vector (lexx (0 : R)) (fun j : 'I_k.+1 => (0 : V)).
exists w; by rewrite scale0r in hw.
Qed.
End Scaling.
