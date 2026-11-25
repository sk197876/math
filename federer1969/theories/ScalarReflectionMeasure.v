(** Scalar reflection measure identity supporting normal-choice independence
    in Federer (1969), 2.10.30, p. 195. Use the already proved isometry
    invariance of Hausdorff length and its equality with scalar Lebesgue
    measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground HausdorffLengthMaps HausdorffLengthReal LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_reflection_preserves_length]: supporting
    unchanged section length after reversing the normal
    in 2.10.30, p. 195. Arbitrary subsets,
    including nonmeasurable and unbounded ones, are allowed. *)
Theorem scalar_reflection_preserves_length (R : realType) (A : set (real_line_metric R)) :
  lebesgue_scalar_measure ((fun t : real_line_metric R=> -t) @^-1` A)=lebesgue_scalar_measure A.
Proof.
pose f (t : real_line_metric R) : real_line_metric R := -t.
have hd s t : mdist (f s) (f t)<=mdist s t.
  have he : -s-(-t)= -(s-t) by rewrite opprB opprK addrC.
  by rewrite /f !real_line_metric_distanceE he normrN.
have hk : cancel f f by move=> t; rewrite /f opprK.
have hh := hausdorff_length_retracted_isometry hd hd hk A.
rewrite hausdorff_length_real_eq_lebesgue in hh.
have he : f @` A=f @^-1` A.
  apply/seteqP; split=> t.
  - move=> [s hs <-]; change (A (f (f s))); by rewrite hk.
  - move=> ht; exists (f t)=> //; exact: hk.
by rewrite he in hh.
Qed.
