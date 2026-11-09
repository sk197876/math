(** Federer (1969), 3.3.20, p. 306:
    independent laws of the original fixed-binary factor. *)
From mathcomp Require Import all_boot all_algebra reals classical_sets.
From Federer Require Import RealMetricBackground PowerCantorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_binary_power_cantor_set]: the original
    A(m,n) with every n_j=2 in 3.3.20,
    p. 306. The positive unit gauge coefficient
    is a supporting normalization; carrier invariance back
    to every original positive book coefficient is proved
    downstream. Compactness, masses and projections are not
    part of these laws. *)
Definition is_binary_power_cantor_set (R:realType) (m:R)
    (A:set (real_line_metric R)):Prop:=
  exists f,is_power_cantor_pair 1 m (fun _:nat=>2%N) A f.
