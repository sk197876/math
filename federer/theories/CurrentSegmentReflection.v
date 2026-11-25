(** Federer (1969), 4.1.8, p. 362: reversing
    the original affine segment changes t to 1-t.
    These algebraic facts retain the original containing
    domain and do not assume its convexity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring lra.
From Federer Require Import GrassmannAbbreviations ConvexMetricSegment CurrentSegmentMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_segment_parameter_reflection]: the
    original segment with endpoints exchanged is the
    original path at parameter 1-t, supporting
    Federer 4.1.8, p. 362. *)
Lemma current_segment_parameter_reflection (R:realType) n (u v:R_n R n) t:
  metric_segment_point u v (1-t)=metric_segment_point v u t.
Proof.
rewrite !current_segment_point_original_formula.
have h:1-(1-t)=t by ring.
by rewrite h addrC.
Qed.

(** Source for [current_segment_domain_reversed]: every
    original containing domain also contains the reversed
    segment, supporting Federer 4.1.8, p. 362. *)
Lemma current_segment_domain_reversed (R:realType) n (A:set (R_n R n)) u v:
  @is_current_segment_domain R n A u v ->@is_current_segment_domain R n A v u.
Proof.
move=>hSegment t ht.
have ht':1-t \in `[0,1].
  move:ht;rewrite !in_itv /=;move=>/andP [h0 h1];apply/andP;split;lra.
rewrite -current_segment_parameter_reflection.
exact:(@hSegment (1-t) ht').
Qed.
