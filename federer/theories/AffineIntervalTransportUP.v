(** Federer (1969), 3.3.20, pp. 307–308:
    independent laws for actual interval transport under a positive similarity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_affine_interval_transport]: independent
    exact original-set image law for the interval
    similarities used in 3.3.20, pp. 307–308.
    Recursion, Cantor-set identity, measure scaling and
    projection conclusions are not defining assumptions. *)
Definition is_affine_interval_transport (R:realType) (a r:R)
    (M:compact_real_intervals R->compact_real_intervals R):Prop:=
  forall S,val (M S)=(fun x:R=>a+r * x) @` val S.

(** Source for [affine_interval_transport_unique]: uniqueness
    of the original interval transport from its exact
    set-image law, supporting 3.3.20, pp. 307–308. *)
Lemma affine_interval_transport_unique (R:realType) (a r:R) M N:
  is_affine_interval_transport a r M ->is_affine_interval_transport a r N ->M=N.
Proof.
move=>hM hN;apply:funext=>S;apply:val_inj;by rewrite hM hN.
Qed.
