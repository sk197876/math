(** Private existence proof for the truncated
    distance in Federer (1969), 3.1.13,
    p. 224. Adjoining the cap one
    gives a nonempty real infimum problem
    even for a whole-space cover member. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import TruncatedComplementDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [truncated_complement_distance_exists]:
    the truncated distance of Federer
    3.1.13, p. 224, exists
    for every cover member, including the
    whole space. Only complete-real infimum
    background is used in this private witness. *)
Theorem truncated_complement_distance_exists (R : realType) (X : metricType R)
    (T : set X) :
  exists d : X->R, is_truncated_complement_distance T d.
Proof.
pose S x := [set 1] `|` ((fun y=>mdist x y) @` (~` T)).
have hn x : S x!=set0 by exists 1; left.
have hl x : has_lbound (S x).
  exists 0=>r [->|[y hy <-]]; [exact: ler01|exact: mdist_ge0].
exists (fun x=>inf (S x)); constructor.
- by move=>x; apply: (ge_inf (hl x)); left.
- by move=>x y hy; apply: (ge_inf (hl x)); right; exists y.
- move=>x c hc hlow; apply: lb_le_inf; first exact: hn x.
  move=>r [->|[y hy <-]]; [exact hc|exact: hlow y hy].
Qed.
