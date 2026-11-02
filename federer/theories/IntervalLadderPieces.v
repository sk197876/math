(** Federer (1969), 2.2.9, p. 65: construct small open intervals with
    closures inside a parent interval, losing only countably many endpoints.
    Two reflected abstract ladders approach the parent's endpoints. The two
    families meet only at the midpoint, which is among the countably many
    omitted endpoints. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals IntervalLadderUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_ladder_endpoints]: supporting interval
    construction for Federer 2.2.9, p. 65. The boolean selects
    the right or left half of the parent; the natural number
    selects a consecutive pair of ladder points. *)
Definition interval_ladder_endpoints (R : realType) (a b : R)
    (d : nat -> R) (p : bool * nat) : R * R :=
  if p.1 then (b-d p.2, b-d p.2.+1) else (a+d p.2.+1, a+d p.2).

(** Source for [interval_ladder_endpoint_set]: supporting
    countable exceptional set in Federer 2.2.9, p. 65:
    all endpoints of the two reflected ladders, including the midpoint. *)
Definition interval_ladder_endpoint_set (R : realType) (a b : R)
    (d : nat -> R) : set (real_line_metric R) :=
  (fun p : bool * nat => if p.1 then b-d p.2 else a+d p.2) @` setT.

(** Source for [interval_ladder_endpoint_countable]: supporting
    countability in Federer 2.2.9, p. 65: the endpoints
    form the image of the countable set of boolean-natural pairs. *)
Lemma interval_ladder_endpoint_countable (R : realType) (a b : R) d :
  countable (interval_ladder_endpoint_set a b d).
Proof. apply: sub_countable (card_image_le _ _) _; exact: countableP. Qed.

(** Source for [interval_ladder_piece_ordered]: supporting
    nonemptiness of the interval children in Federer 2.2.9,
    p. 65, from strict decrease of the given ladder. *)
Lemma interval_ladder_piece_ordered (R : realType) (a b e : R) d
    (hd : is_small_interval_ladder ((b-a)/2) e d) p :
  (interval_ladder_endpoints a b d p).1 < (interval_ladder_endpoints a b d p).2.
Proof.
case: p=> [[] n] /=; rewrite /interval_ladder_endpoints /=.
- by rewrite ltrD2l ltrN2; exact: interval_ladder_decreases hd n.
- by rewrite ltrD2l; exact: interval_ladder_decreases hd n.
Qed.

(** Source for [interval_ladder_piece_inside]: supporting
    closure containment in Federer 2.2.9, p. 65: both
    endpoints of every child lie strictly inside the parent. *)
Lemma interval_ladder_piece_inside (R : realType) (a b e : R) d
    (hd : is_small_interval_ladder ((b-a)/2) e d) p : a < b ->
  a < (interval_ladder_endpoints a b d p).1 /\
  (interval_ladder_endpoints a b d p).2 < b.
Proof.
move=> hab.
have hh : 0 < b-a by rewrite subr_gt0.
have hhalf : (b-a)/2 < b-a.
  by rewrite ltr_pdivrMr ?ltr0n // -{1}[b-a]mulr1 (ltr_pM2l hh) ltr1n.
have hbnd n : d n < b-a.
  apply: le_lt_trans _ hhalf.
  rewrite -(interval_ladder_start hd); exact: (@interval_ladder_antitone R _ e d hd 0%N n (leq0n n)).
case: p=> [[] n] /=; rewrite /interval_ladder_endpoints /=; split.
- by rewrite ltrBrDl -ltrBrDr; exact: hbnd.
- by rewrite ltrBlDl ltrDr; exact: interval_ladder_positive hd n.+1.
- by rewrite ltrDl; exact: interval_ladder_positive hd n.+1.
- by rewrite -ltrBrDl; exact: hbnd.
Qed.

(** Source for [interval_ladder_piece_length]: supporting strict
    diameter bound in Federer 2.2.9, p. 65: each interval
    length is a successive ladder gap and hence smaller than e. *)
Lemma interval_ladder_piece_length (R : realType) (a b e : R) d
    (hd : is_small_interval_ladder ((b-a)/2) e d) p :
  (interval_ladder_endpoints a b d p).2 - (interval_ladder_endpoints a b d p).1 < e.
Proof.
case: p=> [[] n] /=; rewrite /interval_ladder_endpoints /=.
- rewrite [b-d n.+1]addrC addrKA opprK addrC; exact: interval_ladder_gap hd n.
- rewrite [a+d n]addrC addrKA; exact: interval_ladder_gap hd n.
Qed.

(** Source for [interval_ladder_pieces_disjoint]: supporting
    sibling disjointness in Federer 2.2.9, p. 65: ordered
    ladder intervals have disjoint interiors. Their closures are
    allowed to share endpoints, as the printed construction requires. *)
Lemma interval_ladder_pieces_disjoint (R : realType) (a b e : R) d
    (hd : is_small_interval_ladder ((b-a)/2) e d) p q : p <> q ->
  real_open_interval (interval_ladder_endpoints a b d p).1 (interval_ladder_endpoints a b d p).2 `&`
  real_open_interval (interval_ladder_endpoints a b d q).1 (interval_ladder_endpoints a b d q).2 = set0.
Proof.
have hcross i j : a+d i <= b-d j.
  rewrite lerBrDr -addrA -lerBrDl.
  have hi := @interval_ladder_antitone R _ e d hd 0%N i (leq0n i).
  have hj := @interval_ladder_antitone R _ e d hd 0%N j (leq0n j).
  have h := lerD hi hj; by rewrite (interval_ladder_start hd) -splitr in h.
case: p=> [[] i]; case: q=> [[] j] hne; rewrite /interval_ladder_endpoints /=.
- case: (ltngtP i j)=> hij.
  + apply: real_open_intervals_ordered_disjoint.
    rewrite lerD2l lerN2; exact: (@interval_ladder_antitone R _ e d hd _ _ hij).
  + rewrite setIC; apply: real_open_intervals_ordered_disjoint.
    rewrite lerD2l lerN2; exact: (@interval_ladder_antitone R _ e d hd _ _ hij).
  + exfalso; apply: hne; by rewrite hij.
- rewrite setIC; apply: real_open_intervals_ordered_disjoint; exact: hcross.
- apply: real_open_intervals_ordered_disjoint; exact: hcross.
- case: (ltngtP i j)=> hij.
  + rewrite setIC; apply: real_open_intervals_ordered_disjoint.
    rewrite lerD2l; exact: (@interval_ladder_antitone R _ e d hd _ _ hij).
  + apply: real_open_intervals_ordered_disjoint.
    rewrite lerD2l; exact: (@interval_ladder_antitone R _ e d hd _ _ hij).
  + exfalso; apply: hne; by rewrite hij.
Qed.

(** Source for [interval_ladder_pieces_cover_off_endpoints]: supporting
    cover argument for Federer 2.2.9, p. 65. The first ladder point below
    the distance to the nearer parent endpoint determines the unique child,
    unless the point is itself an endpoint. *)
Lemma interval_ladder_pieces_cover_off_endpoints (R : realType) (a b e : R) d
    (hd : is_small_interval_ladder ((b-a)/2) e d) (x : real_line_metric R) :
  real_open_interval a b x -> ~ interval_ladder_endpoint_set a b d x ->
  exists p, real_open_interval (interval_ladder_endpoints a b d p).1
    (interval_ladder_endpoints a b d p).2 x.
Proof.
move=> [hax hxb] hne.
pose h := (b-a)/2.
have hb : b = a+h+h by rewrite /h -addrA -splitr addrC subrK.
case: (ltgtP x (a+h))=> hx.
- have hr : 0 < x-a by rewrite subr_gt0.
  have hrh : x-a < h by rewrite ltrBlDr addrC.
  have [n [hn hrn]] := interval_ladder_crossing hd hr hrh.
  have hrn' : x-a < d n.
    rewrite lt_neqAle hrn andbT; apply/negP=> /eqP heq; apply: hne.
    exists (false,n)=> //=; by rewrite -heq addrC subrK.
  exists (false,n); rewrite /interval_ladder_endpoints /=; split.
  + by move: hn; rewrite ltrBrDl addrC.
  + by move: hrn'; rewrite ltrBlDr addrC.
- have hr : 0 < b-x by rewrite subr_gt0.
  have hrh : b-x < h by rewrite ltrBlDr hb [h+x]addrC ltrD2r.
  have [n [hn hrn]] := interval_ladder_crossing hd hr hrh.
  have hrn' : b-x < d n.
    rewrite lt_neqAle hrn andbT; apply/negP=> /eqP heq; apply: hne.
    exists (true,n)=> //=; by rewrite -heq subKr.
  exists (true,n); rewrite /interval_ladder_endpoints /=; split.
  + by move: hrn'; rewrite ltrBlDr addrC -ltrBlDr.
  + by move: hn; rewrite ltrBrDl -ltrBrDr.
- exfalso; apply: hne; exists (false,0%N)=> //=.
  by rewrite (interval_ladder_start hd) hx.
Qed.
