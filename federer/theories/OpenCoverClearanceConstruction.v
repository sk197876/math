(** Private complete-real supremum witness
    for Federer (1969), 3.1.13, p. 224.
    The cap one bounds every member of
    the arbitrary original cover family. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import TruncatedComplementDistanceUP TruncatedComplementDistanceSealed
  OpenCoverClearanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_cover_clearance_exists]:
    the supremum in Federer 3.1.13,
    p. 224, exists. Adjoining zero
    handles the empty-family extension; for
    nonempty families it does not change
    the supremum of nonnegative distances. *)
Theorem open_cover_clearance_exists (R : realType) (X : metricType R)
    (Phi : set (set X)) :
  exists rho : X->R, is_open_cover_clearance Phi rho.
Proof.
pose S x := [set 0] `|`
  ((fun T : set X=>TruncatedComplementDistance.value T x) @` Phi).
have hn x : S x!=set0 by exists 0; left.
have hu x : has_ubound (S x).
  exists 1=>r [->|[T hT <-]]; first exact: ler01.
  exact: (truncated_complement_distance_cap (TruncatedComplementDistance.laws T) x).
exists (fun x=>sup (S x)); constructor.
- move=>x; apply: (ub_le_sup (hu x)); by left.
- move=>x T hT; apply: (ub_le_sup (hu x)); right; by exists T.
- move=>x c hc hb; apply: (ge_sup (hn x)).
  move=>r [->|[T hT <-]]; [exact hc|exact: hb T hT].
Qed.
