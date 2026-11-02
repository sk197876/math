(** Federer (1969), 2.2.8, pp. 64–65: a sufficiently small distance forces
    agreement of initial coordinates. Selecting the first different
    coordinate gives the same diameter-versus-distance comparison without
    introducing the intermediate dyadic annulus. The metric remains
    Federer's exact series from 2.2.6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceSpaceUP SequenceCoordinates
  SequenceMetricPrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_sequence_first_difference]: supporting
    choice of the common prefix in Federer 2.2.8, pp. 64–65:
    distinct sequences have a first different coordinate. Only
    natural well ordering and the abstract coordinate injection are used. *)
Lemma positive_sequence_first_difference (R : realType)
    (m n : positive_sequence_space R) : m != n -> exists k,
  positive_sequence_coordinates m k != positive_sequence_coordinates n k /\
  forall i, (i < k)%N -> positive_sequence_coordinates m i = positive_sequence_coordinates n i.
Proof.
move=> hmn.
have hex : exists k, positive_sequence_coordinates m k != positive_sequence_coordinates n k.
  case: (pselect (exists k, positive_sequence_coordinates m k != positive_sequence_coordinates n k))=> h; first exact h.
  exfalso; have he : m = n.
    apply: positive_sequence_extensionality=> k.
    case: (eqVneq (positive_sequence_coordinates m k) (positive_sequence_coordinates n k))=> hk; first exact hk.
    exfalso; apply: h; by exists k.
  by move: hmn; rewrite he eqxx.
have [k hk hmin] := ex_minnP hex.
exists k; split=> // i hi.
case: (eqVneq (positive_sequence_coordinates m i) (positive_sequence_coordinates n i))=> hn; first exact hn.
exfalso; have hki := hmin i hn; by move: hi; rewrite ltnNge hki.
Qed.

(** Source for [positive_sequence_different_coordinate_lower]: Federer
    2.2.8, pp. 64–65, the distance contribution of a different coordinate is
    at least half its weight. This is the contrapositive of the proved
    coordinate recovery estimate *)
Lemma positive_sequence_different_coordinate_lower (R : realType)
    (m n : positive_sequence_space R) k :
  positive_sequence_coordinates m k != positive_sequence_coordinates n k ->
  @sequence_metric_weight R k / 2 <= mdist m n.
Proof.
move=> hk; rewrite leNgt; apply/negP=> hd.
have he := @positive_sequence_small_distance_coordinate R _ _ _
  (positive_sequence_distance_specification R) m n k hd.
by move: hk; rewrite he eqxx.
Qed.
