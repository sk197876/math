(** Federer (1969), 2.10.14, p. 177: alpha_+(x) and alpha_-(x) are the
    one-sided upper limits of distance(g(t),g(x)). Specify this upper limit
    by its eventual upper bounds and use the sealed extended-real infimum of
    2.1.1, p. 51, to prove existence. The boolean side is true on the right
    and false on the left. No variation, continuity, one-sided limit or
    target completeness is assumed. it does not state 2.10.14. Federer's
    erratum, p. 3, book p. 177 line 23, changes the subsequent integral to
    an upper integral; it does not change these jump definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_side_offset]: supporting oriented parameter
    displacement for the one-sided limits in 2.10.14, p. 177.
    A positive offset selects t>x on the right and t<x on the left. *)
Definition curve_side_offset (R : realType) (right : bool) (x t : R) : R :=
  if right then (t-x)%R else (x-t)%R.

(** Source for [curve_side_offset_point]: supporting nonempty
    one-sided neighbourhoods for the upper limits in 2.10.14,
    p. 177. The point at signed offset d has offset d. *)
Lemma curve_side_offset_point (R : realType) (right : bool) (x d : R) :
  curve_side_offset right x (if right then (x+d)%R else (x-d)%R)=d.
Proof. by case: right; rewrite /curve_side_offset /=; lra. Qed.

(** Source for [curve_side_distance_upper_bound]: supporting eventual
    upper-bound predicate for alpha_+ and alpha_- in 2.10.14,
    p. 177. Bounds and the selected upper limit may be infinite. *)
Definition curve_side_distance_upper_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (b : \bar R) :=
  exists d : R, (0<d)%R /\ forall t,
    (0<curve_side_offset right x t<d)%R -> (mdist (g t) (g x))%:E<=b.

(** Source for [is_curve_one_sided_jump]: abstract upper-limit
    specification for alpha_+ and alpha_- in 2.10.14, p. 177.
    Its two laws say precisely that the jump is the infimum of
    all eventual upper bounds; they introduce no unproved axiom. *)
Definition is_curve_one_sided_jump (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (j : \bar R) :=
  (forall b, curve_side_distance_upper_bound g right x b -> j<=b) /\
  (forall c, (forall b, curve_side_distance_upper_bound g right x b -> c<=b) -> c<=j).

(** Source for [curve_one_sided_jump]: direct alpha_+ or alpha_-
    of 2.10.14, p. 177, selected using the existing sealed
    extended-real infimum. Later arguments use its order laws. *)
Definition curve_one_sided_jump (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) :=
  extended_real_inf (curve_side_distance_upper_bound g right x).

(** Source for [curve_right_jump_size]: direct alpha_+(x) in
    2.10.14, p. 177, the right-hand distance upper limit. *)
Definition curve_right_jump_size (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) := curve_one_sided_jump g true x.

(** Source for [curve_left_jump_size]: direct alpha_-(x) in
    2.10.14, p. 177, the left-hand distance upper limit. *)
Definition curve_left_jump_size (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) := curve_one_sided_jump g false x.

(** Source for [curve_one_sided_jump_specification]: proved
    specification of the two upper limits in 2.10.14, p. 177.
    The witness uses only the existing infimum interface. *)
Lemma curve_one_sided_jump_specification (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) :
  is_curve_one_sided_jump g right x (curve_one_sided_jump g right x).
Proof.
constructor; [exact: extended_real_inf_lower|exact: extended_real_inf_greatest].
Qed.

(** Source for [curve_side_distance_upper_bound_nonnegative]: supporting
    nonnegativity of the one-sided distance upper limits in
    2.10.14, p. 177. Each positive one-sided neighbourhood
    contains a point, whose nonnegative distance bounds zero. *)
Lemma curve_side_distance_upper_bound_nonnegative (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (b : \bar R) :
  curve_side_distance_upper_bound g right x b -> 0<=b.
Proof.
move=> [d [hd hb]].
have he : (0<d/2<d)%R by apply/andP; split; lra.
have hh := hb (if right then (x+d/2)%R else (x-d/2)%R).
rewrite curve_side_offset_point in hh.
apply: le_trans (_ : 0<=(mdist (g (if right then (x+d/2)%R else (x-d/2)%R)) (g x))%:E)
  (hh he).
by rewrite lee_fin mdist_ge0.
Qed.

(** Source for [curve_one_sided_jump_nonnegative]: direct supporting
    sign of alpha_+ and alpha_- in 2.10.14, p. 177,
    without assuming that g has finite variation. *)
Lemma curve_one_sided_jump_nonnegative (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) : 0<=curve_one_sided_jump g right x.
Proof.
apply: extended_real_inf_greatest=> b hb.
exact: curve_side_distance_upper_bound_nonnegative hb.
Qed.

(** Source for [curve_one_sided_jump_upper_bound]: supporting eventual-
    bound rule for the upper limits in 2.10.14, p. 177. *)
Lemma curve_one_sided_jump_upper_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (b : \bar R) :
  curve_side_distance_upper_bound g right x b -> curve_one_sided_jump g right x<=b.
Proof. exact: extended_real_inf_lower. Qed.

(** Source for [curve_one_sided_jump_strict_bound]: supporting
    approximation of alpha_+ and alpha_- from above, 2.10.14,
    p. 177. A strict bound on the upper limit is a strict
    distance bound on a sufficiently short one-sided interval. *)
Lemma curve_one_sided_jump_strict_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (b : \bar R) :
  curve_one_sided_jump g right x<b -> exists d : R, (0<d)%R /\
    forall t, (0<curve_side_offset right x t<d)%R -> (mdist (g t) (g x))%:E<b.
Proof.
move=> hj.
have [c [hc hcb]] : exists c, curve_side_distance_upper_bound g right x c /\ c<b.
  apply: contrapT=> hn.
  have hl : b<=curve_one_sided_jump g right x.
    apply: extended_real_inf_greatest=> c hc.
    rewrite leNgt; apply/negP=> hcb; apply: hn; by exists c.
  by have hh := lt_le_trans hj hl; rewrite ltxx in hh.
have [d [hd hb]] := hc; exists d; split=> // t ht.
exact: le_lt_trans (hb t ht) hcb.
Qed.

(** Source for [curve_one_sided_jump_lower_bound]: supporting lower-
    bound rule for the upper limits in 2.10.14, p. 177.
    A distance at least c in every one-sided neighbourhood
    forces c below the upper limit, with infinite c permitted. *)
Lemma curve_one_sided_jump_lower_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (c : \bar R) :
  (forall d : R, (0<d)%R -> exists t, (0<curve_side_offset right x t<d)%R /\
    c<=(mdist (g t) (g x))%:E) -> c<=curve_one_sided_jump g right x.
Proof.
move=> h; apply: extended_real_inf_greatest=> b [d [hd hb]].
have [t [ht hct]] := h d hd.
exact: le_trans hct (hb t ht).
Qed.
