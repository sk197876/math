(** Federer (1969), 3.1.13, p. 224:
    the supremum of the truncated complement
    distances is specified by its order laws.
    An explicit zero lower bound extends it
    to an empty cover family. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import TruncatedComplementDistanceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_open_cover_clearance]:
    the unscaled supremum in the definition
    of h in Federer 3.1.13, p. 224.
    No countability or local finiteness is
    assumed of the original family. *)
Record is_open_cover_clearance (R : realType) (X : metricType R)
    (Phi : set (set X)) (rho : X->R) : Prop := {
  (** Source for [open_cover_clearance_nonnegative]:
      the nonnegative supremum used in
      Federer 3.1.13, p. 224. *)
  open_cover_clearance_nonnegative : forall x, 0<=rho x;
  (** Source for [open_cover_clearance_upper]:
      each truncated distance is bounded
      by the supremum in Federer
      3.1.13, p. 224. *)
  open_cover_clearance_upper : forall x T, Phi T ->
    TruncatedComplementDistance.value T x<=rho x;
  (** Source for [open_cover_clearance_least]:
      leastness of the supremum in
      Federer 3.1.13, p. 224.
      The zero clause handles an empty family. *)
  open_cover_clearance_least : forall x c, 0<=c ->
    (forall T, Phi T -> TruncatedComplementDistance.value T x<=c) -> rho x<=c
}.
