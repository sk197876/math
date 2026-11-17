(** Federer (1969), 3.4.12, p. 339: a complex
    polynomial on an original real parameter has the same
    vector-valued real power sum. Reuse the scalar embedding laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_real_power_sum]: exact parameter restriction
    for finite coefficient comparisons in the complex extension of
    3.4.6(2), p. 322, required by 3.4.12, p. 339. *)
Lemma complex_real_power_sum (R:realFieldType) k (a:nat->ComplexScalars.C R) (t:R):
  (\sum_(i<k) (ComplexScalars.embed R t)^+i*a i)=
    \sum_(i<k) t^+i*:(a i:restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Proof.
apply:eq_bigr=>i _.
change ((ComplexScalars.embed R t)^+i*a i=ComplexScalars.embed R (t^+i)*a i).
by rewrite rmorphXn.
Qed.
