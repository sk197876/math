(** Federer (1969), 2.10.28(1), proof p. 192: the two overlap inequalities
    used to enlarge a test interval through its left and right boundary
    members. Derive them from the abstract decreasing-increment law, without
    choosing a formula for h. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [concave_interval_overlap_submodular]: supporting
    one-sided interval enlargement inequality in
    2.10.28(1), p. 192. For a<=b<=c<=d,
    the costs of the union and intersection
    of [a,c] and [b,d] sum to at most
    their two original costs. Degenerate overlaps
    are included under h(0)=0. *)
Lemma concave_interval_overlap_submodular (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) a b c d :
  a<=b -> b<=c -> c<=d ->
  h (d-a)+h (c-b)<=h (c-a)+h (d-b).
Proof.
move=> hab hbc hcd.
have hx : 0<=c-b by lra.
have hxy : c-b<=c-a by lra.
have hr : 0<=d-c by lra.
have hh := @concave_interval_gauge_decreasing_increments R h hg (c-b) (c-a) (d-c) hx hxy hr.
have he1 : c-a+(d-c)=d-a by lra.
have he2 : c-b+(d-c)=d-b by lra.
rewrite he1 he2 in hh; lra.
Qed.

(** Source for [concave_interval_two_boundary_extension]:
    supporting sum of the two displayed enlargement
    inequalities in the proof of 2.10.28(1),
    p. 192. The test interval [a,b]
    meets the left member [v0,v1] and
    right member [w0,w1]; enclosing both
    costs at most the original test cost
    plus the two losses from clipping. *)
Lemma concave_interval_two_boundary_extension (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) a b v0 v1 w0 w1 :
  v0<=a -> a<=v1 -> v1<=w0 -> w0<=b -> b<=w1 ->
  h (w1-v0)<=h (b-a)+h (v1-v0)-h (v1-a)+h (w1-w0)-h (b-w0).
Proof.
move=> h0 h1 h2 h3 h4.
have hvb : v1<=b := le_trans h2 h3.
have hvw : v0<=w0 := le_trans (le_trans h0 h1) h2.
have hleft := @concave_interval_overlap_submodular R h hg v0 a v1 b h0 h1 hvb.
have hright := @concave_interval_overlap_submodular R h hg v0 w0 b w1 hvw h3 h4.
lra.
Qed.
