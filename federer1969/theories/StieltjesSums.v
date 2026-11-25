(** Federer (1969), 2.5.17, pp. 110-111: the Riemann-Stieltjes sums
    sum_{i=1}^n f(u_i) [g(t_{i+1}) - g(t_i)] corresponding to the finite
    sequences a = t_1 <= u_1 <= t_2 <= u_2 <= ... <= t_n <= u_n <= t_{n+1} =
    b, and the estimate that two such sums with t_{i+1} - t_i < delta differ
    by at most 2 sup{|f(u) - f(v)| : |u - v| <= delta} times the absolute
    increment sum of g over the common refinement. A sequence is a single
    nondecreasing list alternating points and tags. The comparison of a sum
    with the left sum over a refinement proceeds cell by cell, splitting the
    refinement at the right end of each cell. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From mathcomp Require Import ring lra.
From Federer Require Import CurveVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section StieltjesSums.
Variable R : realType.
Variables f g : R -> R.

(** Source for [stieltjes_sum]: the sum sum_i f(u_i) [g(t_{i+1}) - g(t_i)]
    of Federer 2.5.17, p. 110, over the alternating list
    t_1, u_1, t_2, u_2, ..., t_n, u_n, t_{n+1}. *)
Fixpoint stieltjes_sum (w : seq R) : R :=
  match w with
  | t :: u :: ((t' :: _) as rest) => f u * (g t' - g t) + stieltjes_sum rest
  | _ => 0
  end.

(** Source for [tagged_points]: the points t_1, ..., t_{n+1} of a
    sequence of Federer 2.5.17, p. 110. *)
Fixpoint tagged_points (w : seq R) : seq R :=
  match w with
  | t :: _ :: rest => t :: tagged_points rest
  | [:: t] => [:: t]
  | [::] => [::]
  end.

(** Source for [tagged_mesh_lt]: the condition t_{i+1} - t_i < delta for
    i = 1, ..., n of Federer 2.5.17, p. 111. *)
Fixpoint tagged_mesh_lt (d : R) (w : seq R) : bool :=
  match w with
  | t :: _ :: ((t' :: _) as rest) => (t' - t < d) && tagged_mesh_lt d rest
  | _ => true
  end.

(** Source for [is_tagged_partition]: a finite sequence
    a = t_1 <= u_1 <= ... <= u_n <= t_{n+1} = b of Federer 2.5.17, p. 110,
    with n >= 0; the empty sum of a single point arises only for a = b. *)
Definition is_tagged_partition (a b : R) (w : seq R) : Prop :=
  sorted <=%O w /\ odd (size w) /\ head a w = a /\ last a w = b.

(** Source for [left_sum]: supporting sum over a list of points with
    each tag at the left end of its cell, used for refinements in
    Federer 2.5.17, p. 111. *)
Fixpoint left_sum (s : seq R) : R :=
  match s with
  | t :: ((t' :: _) as rest) => f t * (g t' - g t) + left_sum rest
  | _ => 0
  end.

(** Source for [absolute_chain]: supporting sum of the absolute
    increments |g(t_{i+1}) - g(t_i)| over a list of points, bounded by
    V_a^b g in Federer 2.5.17, p. 111. *)
Fixpoint absolute_chain (s : seq R) : R :=
  match s with
  | t :: ((t' :: _) as rest) => `|g t' - g t| + absolute_chain rest
  | _ => 0
  end.

(** Source for [stieltjes_sum_cons]: supporting one step of the sum,
    Federer 2.5.17, p. 110. *)
Lemma stieltjes_sum_cons (t u t' : R) (rest : seq R) :
  stieltjes_sum (t :: u :: t' :: rest) = f u * (g t' - g t) + stieltjes_sum (t' :: rest).
Proof. by []. Qed.

(** Source for [left_sum_cons2]: supporting one step of the left sum,
    Federer 2.5.17, p. 111. *)
Lemma left_sum_cons2 (t t' : R) (s : seq R) :
  left_sum (t :: t' :: s) = f t * (g t' - g t) + left_sum (t' :: s).
Proof. by []. Qed.

(** Source for [absolute_chain_cons2]: supporting one step of the
    absolute increment sum, Federer 2.5.17, p. 111. *)
Lemma absolute_chain_cons2 (t t' : R) (s : seq R) :
  absolute_chain (t :: t' :: s) = `|g t' - g t| + absolute_chain (t' :: s).
Proof. by []. Qed.

(** Source for [tagged_points_cons]: supporting one step of the points,
    Federer 2.5.17, p. 110. *)
Lemma tagged_points_cons (t u : R) (rest : seq R) :
  tagged_points (t :: u :: rest) = t :: tagged_points rest.
Proof. by []. Qed.

(** Source for [tagged_points_head]: the first point of a nonempty
    sequence, Federer 2.5.17, p. 110. *)
Lemma tagged_points_head (t : R) (w : seq R) : head 0 (tagged_points (t :: w)) = t.
Proof. by case: w. Qed.

(** Source for [tagged_mesh_lt_cons]: supporting one step of the mesh
    condition, Federer 2.5.17, p. 111. *)
Lemma tagged_mesh_lt_cons (d t u t' : R) (rest : seq R) :
  tagged_mesh_lt d (t :: u :: t' :: rest) = (t' - t < d) && tagged_mesh_lt d (t' :: rest).
Proof. by []. Qed.

(** Source for [absolute_chain_nonnegative]: supporting nonnegativity
    of the absolute increment sum, Federer 2.5.17, p. 111. *)
Lemma absolute_chain_nonnegative (s : seq R) : 0 <= absolute_chain s.
Proof.
elim: s=> [//|t s ih]; case: s ih=> [//|t' s] ih.
by rewrite absolute_chain_cons2 addr_ge0.
Qed.

(** Source for [left_sum_cat]: supporting splitting of a left sum at a
    junction, Federer 2.5.17, p. 111. *)
Lemma left_sum_cat (s1 s2 : seq R) : s1 <> [::] -> s2 <> [::] ->
  left_sum (s1 ++ s2) =
    left_sum s1 + f (last 0 s1) * (g (head 0 s2) - g (last 0 s1)) + left_sum s2.
Proof.
elim: s1=> [//|t s1 ih] _ h2; case: s1 ih=> [_|t1 s1 ih].
- by case: s2 h2=> [//|t2 s2] _; rewrite /=; ring.
- have hne : t1 :: s1 <> [::] by [].
  have hih := ih hne h2.
  by rewrite !cat_cons left_sum_cons2 hih !left_sum_cons2 !last_cons; ring.
Qed.

(** Source for [left_sum_rcons]: supporting extension of a left sum by
    a final point, Federer 2.5.17, p. 111. *)
Lemma left_sum_rcons (s : seq R) (b : R) : s <> [::] ->
  left_sum (rcons s b) = left_sum s + f (last 0 s) * (g b - g (last 0 s)).
Proof. by move=> hs; rewrite -cats1 (left_sum_cat hs) //= addr0. Qed.

(** Source for [absolute_chain_cat]: supporting splitting of the
    absolute increment sum at a junction, Federer 2.5.17, p. 111. *)
Lemma absolute_chain_cat (s1 s2 : seq R) : s1 <> [::] -> s2 <> [::] ->
  absolute_chain (s1 ++ s2) =
    absolute_chain s1 + `|g (head 0 s2) - g (last 0 s1)| + absolute_chain s2.
Proof.
elim: s1=> [//|t s1 ih] _ h2; case: s1 ih=> [_|t1 s1 ih].
- by case: s2 h2=> [//|t2 s2] _; rewrite /=; ring.
- have hne : t1 :: s1 <> [::] by [].
  have hih := ih hne h2.
  by rewrite !cat_cons absolute_chain_cons2 hih !absolute_chain_cons2 !last_cons; ring.
Qed.

(** Source for [absolute_chain_rcons]: supporting extension of the
    absolute increment sum by a final point, Federer 2.5.17, p. 111. *)
Lemma absolute_chain_rcons (s : seq R) (b : R) : s <> [::] ->
  absolute_chain (rcons s b) = absolute_chain s + `|g b - g (last 0 s)|.
Proof. by move=> hs; rewrite -cats1 (absolute_chain_cat hs) //= addr0. Qed.

(** Source for [left_sum_constant]: a constant list has left sum zero,
    the degenerate cells of Federer 2.5.17, p. 110. *)
Lemma left_sum_constant (s : seq R) (c : R) : (forall x, x \in s -> x = c) -> left_sum s = 0.
Proof.
elim: s=> [//|t s ih] hall; case: s ih hall=> [//|t' s] ih hall.
have ht : t = c by apply: hall; rewrite inE eqxx.
have ht' : t' = c by apply: hall; rewrite !inE eqxx orbT.
rewrite left_sum_cons2 ih; last by move=> x hx; apply: hall; rewrite inE hx orbT.
by rewrite ht ht' subrr mulr0 add0r.
Qed.

(** Source for [absolute_chain_constant]: a constant list has absolute
    increment sum zero, Federer 2.5.17, p. 110. *)
Lemma absolute_chain_constant (s : seq R) (c : R) :
  (forall x, x \in s -> x = c) -> absolute_chain s = 0.
Proof.
elim: s=> [//|t s ih] hall; case: s ih hall=> [//|t' s] ih hall.
have ht : t = c by apply: hall; rewrite inE eqxx.
have ht' : t' = c by apply: hall; rewrite !inE eqxx orbT.
rewrite absolute_chain_cons2 ih; last by move=> x hx; apply: hall; rewrite inE hx orbT.
by rewrite ht ht' subrr normr0 add0r.
Qed.

(** Source for [cell_left_estimate]: the estimate of one cell of a
    Riemann-Stieltjes sum against the left sum over a refinement of the
    cell, Federer 2.5.17, p. 111: the difference is
    sum_j (f(u) - f(s_j)) [g(s_{j+1}) - g(s_j)]. *)
Lemma cell_left_estimate (u om : R) (c : seq R) : c <> [::] ->
  (forall s, s \in c -> `|f u - f s| <= om) ->
  `|f u * (g (last 0 c) - g (head 0 c)) - left_sum c| <= om * absolute_chain c.
Proof.
elim: c=> [//|t c ih] _ hall; case: c ih hall=> [_ _|t' c ih hall].
- by rewrite /= subrr mulr0 subr0 normr0 mulr0.
- have hom : `|f u - f t| <= om by apply: hall; rewrite inE eqxx.
  have hrest : forall s, s \in t' :: c -> `|f u - f s| <= om.
    by move=> s hs; apply: hall; rewrite inE hs orbT.
  have hne : t' :: c <> [::] by [].
  have hih := ih hne hrest.
  rewrite left_sum_cons2 absolute_chain_cons2 !last_cons.
  have -> : f u * (g (last t' c) - g t) - (f t * (g t' - g t) + left_sum (t' :: c))
    = (f u - f t) * (g t' - g t) + (f u * (g (last t' c) - g t') - left_sum (t' :: c)) by ring.
  apply: le_trans (ler_normD _ _) _; rewrite (mulrDr om); apply: lerD.
  + by rewrite normrM; exact (ler_wpM2r (normr_ge0 _) hom).
  + by move: hih; rewrite !last_cons.
Qed.

(** Source for [tagged_points_subseq]: the points form a subsequence of
    the alternating sequence, Federer 2.5.17, p. 110. *)
Lemma tagged_points_subseq (w : seq R) : subseq (tagged_points w) w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u rest]] //= hsize.
- by rewrite eqxx.
- rewrite eqxx; apply: subseq_trans (subseq_cons _ u).
  by apply: ih; rewrite -ltnS; exact: ltnW.
Qed.

(** Source for [tagged_points_sorted]: the points are nondecreasing,
    Federer 2.5.17, p. 110. *)
Lemma tagged_points_sorted (w : seq R) : sorted <=%O w -> sorted <=%O (tagged_points w).
Proof. by move=> hs; exact (subseq_sorted le_trans (tagged_points_subseq w) hs). Qed.

(** Source for [tagged_points_mem]: a point belongs to the sequence,
    Federer 2.5.17, p. 110. *)
Lemma tagged_points_mem (w : seq R) : {subset tagged_points w <= w}.
Proof. exact: mem_subseq (tagged_points_subseq w). Qed.

(** Source for [tagged_points_head_mem]: the first point t_1 = a belongs
    to the points, Federer 2.5.17, p. 110. *)
Lemma tagged_points_head_mem (t : R) (w : seq R) : t \in tagged_points (t :: w).
Proof. by case: w=> [|u w] /=; rewrite inE eqxx. Qed.

(** Source for [tagged_points_last_mem]: the last point t_{n+1} = b
    belongs to the points, Federer 2.5.17, p. 110. *)
Lemma tagged_points_last_mem (w : seq R) (a : R) : odd (size w) -> last a w \in tagged_points w.
Proof.
have [n] := ubnP (size w); elim: n w a=> // n ih w a hsize hodd.
case: w hsize hodd=> [|t [|u [|t' rest']]] hsize hodd //.
- by rewrite inE eqxx.
- rewrite tagged_points_cons inE; apply/orP; right.
  apply: (ih (t' :: rest') t).
  - by move: hsize; rewrite /= ltnS; exact: ltnW.
  - by move: hodd; rewrite /= negbK.
Qed.

(** Source for [sorted_mem_bounds]: supporting bounds of the members of
    a nondecreasing list by its ends, Federer 2.5.17, p. 110. *)
Lemma sorted_mem_bounds (s : seq R) (x : R) :
  sorted <=%O s -> x \in s -> head 0 s <= x <= last 0 s.
Proof.
by move=> hs hx; rewrite (sorted_head_le 0 hs hx) (sorted_le_last 0 hs hx).
Qed.

(** Source for [sorted_head_eq]: supporting identification of the head
    of a nondecreasing list with a least member, Federer 2.5.17,
    p. 111. *)
Lemma sorted_head_eq (s : seq R) (a : R) :
  sorted <=%O s -> a \in s -> (forall x, x \in s -> a <= x) -> head 0 s = a.
Proof.
move=> hs ha hall; apply/le_anti; rewrite (sorted_head_le 0 hs ha) /=.
by case: s hs ha hall=> [//|t s] _ _ hall; apply: hall; rewrite inE eqxx.
Qed.

(** Source for [sorted_last_eq]: supporting identification of the last
    member of a nondecreasing list with a greatest member, Federer
    2.5.17, p. 111. *)
Lemma sorted_last_eq (s : seq R) (b : R) :
  sorted <=%O s -> b \in s -> (forall x, x \in s -> x <= b) -> last 0 s = b.
Proof.
move=> hs hb hall; apply/le_anti; rewrite (sorted_le_last 0 hs hb) andbT.
apply: hall; case: s hs hb=> [//|t s] _ _ /=; exact: mem_last.
Qed.

(** Source for [last_nonempty_default]: supporting independence of the
    last element from the default, Federer 2.5.17, p. 111. *)
Lemma last_nonempty_default (s : seq R) (x y : R) : s <> [::] -> last x s = last y s.
Proof. by case: s. Qed.

(** Source for [head_rcons_nonempty]: supporting the head of an
    extended list, Federer 2.5.17, p. 111. *)
Lemma head_rcons_nonempty (s : seq R) (x y : R) : s <> [::] -> head x (rcons s y) = head x s.
Proof. by case: s. Qed.

(** Source for [filter_lt_head]: supporting the head of the part of a
    list below a bound, Federer 2.5.17, p. 111. *)
Lemma filter_lt_head (s : seq R) (c : R) :
  s <> [::] -> head 0 s < c -> head 0 [seq x <- s | x < c] = head 0 s.
Proof. by case: s=> [//|t s] _ /= ->. Qed.




(** Source for [tagged_partition_head0]: t_1 = a, Federer 2.5.17,
    p. 110. *)
Lemma tagged_partition_head0 (a b : R) (w : seq R) : is_tagged_partition a b w -> head 0 w = a.
Proof. by move=> [_ [hodd [hh _]]]; case: w hodd hh. Qed.

(** Source for [tagged_partition_last0]: t_{n+1} = b, Federer 2.5.17,
    p. 110. *)
Lemma tagged_partition_last0 (a b : R) (w : seq R) : is_tagged_partition a b w -> last 0 w = b.
Proof. by move=> [_ [hodd [_ hl]]]; case: w hodd hl. Qed.

(** Source for [tagged_partition_a_mem]: a is a point of the sequence,
    Federer 2.5.17, p. 110. *)
Lemma tagged_partition_a_mem (a b : R) (w : seq R) :
  is_tagged_partition a b w -> a \in tagged_points w.
Proof.
move=> hw; have hh := tagged_partition_head0 hw.
case: w hw hh=> [[_ [h _]]|t w _ /= ->] //.
exact: tagged_points_head_mem.
Qed.

(** Source for [tagged_partition_b_mem]: b is a point of the sequence,
    Federer 2.5.17, p. 110. *)
Lemma tagged_partition_b_mem (a b : R) (w : seq R) :
  is_tagged_partition a b w -> b \in tagged_points w.
Proof.
move=> hw; have [_ [hodd [_ hl]]] := hw; rewrite -hl; exact: tagged_points_last_mem.
Qed.

(** Source for [tagged_partition_points_bounds]: the points lie in
    [a, b], Federer 2.5.17, p. 110. *)
Lemma tagged_partition_points_bounds (a b : R) (w : seq R) (x : R) :
  is_tagged_partition a b w -> x \in tagged_points w -> a <= x <= b.
Proof.
move=> hw hx; have := sorted_mem_bounds hw.1 (tagged_points_mem hx).
by rewrite (tagged_partition_head0 hw) (tagged_partition_last0 hw).
Qed.

(** Source for [tagged_partition_tail]: the sequence after its first
    cell is a sequence from t_2 to b, Federer 2.5.17, p. 110. *)
Lemma tagged_partition_tail (a b t u : R) (rest : seq R) :
  is_tagged_partition a b (t :: u :: rest) ->
  exists t' rest', rest = t' :: rest' /\ a = t /\ t <= u /\ u <= t' /\
    is_tagged_partition t' b (t' :: rest').
Proof.
move=> [hs [hodd [hh hl]]]; case: rest hs hodd hh hl=> [|t' rest'] hs hodd hh hl; first by [].
exists t', rest'; move: hs=> /= /and3P[htu hut' hs'].
split=> //; split; first by move: hh=> /= ->.
split=> //; split=> //; split=> //; split=> //.
by move: hodd; rewrite /= negbK.
Qed.

(** Source for [tagged_refinement_estimate]: the comparison of a
    Riemann-Stieltjes sum with mesh below delta and the left sum over
    a refinement of its points from a to b, Federer 2.5.17, p. 111:
    the difference is at most om times the absolute increment sum,
    where om bounds |f(u) - f(v)| for |u - v| <= delta in [a, b]. *)
Lemma tagged_refinement_estimate (d om : R) (w : seq R) (a b : R) (M : seq R) :
  is_tagged_partition a b w -> tagged_mesh_lt d w ->
  sorted <=%O M -> {subset tagged_points w <= M} -> head 0 M = a -> last 0 M = b ->
  (forall x y, a <= x <= b -> a <= y <= b -> `|x - y| <= d -> `|f x - f y| <= om) ->
  `|stieltjes_sum w - left_sum M| <= om * absolute_chain M.
Proof.
have [n] := ubnP (size w); elim: n w a b M=> // n ih w a b M hsize hw hmesh hM hsub hhead hlast hom.
case: w hsize hw hmesh hsub=> [|t [|u rest]] hsize hw hmesh hsub.
- by case: hw=> [_ [h _]].
- have [_ [_ [hh hl]]] := hw.
  have hat : t = a by move: hh.
  have hbt : t = b by move: hl.
  have hconst : forall x, x \in M -> x = a.
    move=> x hx; have := sorted_mem_bounds hM hx; rewrite hhead hlast -hbt hat.
    by move=> /andP[h1 h2]; apply/le_anti; rewrite h1 h2.
  by rewrite (left_sum_constant hconst) (absolute_chain_constant hconst) mulr0 subr0 normr0.
- have [t' [rest' [hrest [hat [htu [hut' hw']]]]]] := tagged_partition_tail hw.
  subst rest.
  move: hmesh; rewrite tagged_mesh_lt_cons=> /andP[hmesh1 hmesh'].
  have htM : t \in M by apply: hsub; rewrite tagged_points_cons inE eqxx.
  have hsub' : {subset tagged_points (t' :: rest') <= M}.
    by move=> x hx; apply: hsub; rewrite tagged_points_cons inE hx orbT.
  have ht'M : t' \in M by apply: hsub'; exact: tagged_points_head_mem.
  have hbounds : forall x, x \in M -> a <= x <= b.
    by move=> x hx; have := sorted_mem_bounds hM hx; rewrite hhead hlast.
  have ht'b : t' <= b by have /andP[_] := hbounds _ ht'M.
  have hat' : a <= t' by have /andP[] := hbounds _ ht'M.
  have hom' : forall x y, t' <= x <= b -> t' <= y <= b -> `|x - y| <= d -> `|f x - f y| <= om.
    move=> x y /andP[h1 h2] /andP[h3 h4] hxy.
    have hx : a <= x <= b by rewrite h2 andbT; exact: le_trans hat' h1.
    have hy : a <= y <= b by rewrite h4 andbT; exact: le_trans hat' h3.
    exact: hom hx hy hxy.
  have [M1 hM1] : exists M1, M1 = [seq x <- M | x < t'] by eexists.
  have [M2 hM2] : exists M2, M2 = [seq x <- M | t' <= x] by eexists.
  have hsplit : M = M1 ++ M2 by rewrite hM1 hM2; exact: (sorted_split_filter t' hM).
  have hM2ne : M2 <> [::].
    move=> h; have : t' \in M2 by rewrite hM2 mem_filter lexx ht'M.
    by rewrite h.
  have hM2s : sorted <=%O M2 by rewrite hM2; exact (sorted_filter le_trans _ hM).
  have hM2head : head 0 M2 = t'.
    apply: sorted_head_eq=> //; first by rewrite hM2 mem_filter lexx ht'M.
    by move=> x; rewrite hM2 mem_filter=> /andP[].
  have hM2last : last 0 M2 = b.
    by rewrite -hlast hsplit last_cat; exact: (last_nonempty_default 0 (last 0 M1) hM2ne).
  have hsize' : (size (t' :: rest') < n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  have hsub2 : {subset tagged_points (t' :: rest') <= M2}.
    move=> x hx; rewrite hM2 mem_filter (hsub' _ hx) andbT.
    have := sorted_mem_bounds (tagged_points_sorted hw'.1) hx.
    by rewrite tagged_points_head=> /andP[].
  have hih := ih _ _ _ _ hsize' hw' hmesh' hM2s hsub2 hM2head hM2last hom'.
  case: (pselect (M1 = [::]))=> [hM1nil|hM1ne].
  - have htt' : t' <= t.
      rewrite leNgt; apply/negP=> hlt; have : t \in M1 by rewrite hM1 mem_filter hlt htM.
      by rewrite hM1nil.
    have htt'eq : t = t' by apply/le_anti; rewrite (le_trans htu hut') htt'.
    have hMM2 : M = M2 by rewrite hsplit hM1nil.
    rewrite stieltjes_sum_cons htt'eq subrr mulr0 add0r hMM2.
    exact: hih.
  - have hlt : t < t'.
      rewrite lt_neqAle (le_trans htu hut') andbT; apply/eqP=> heq.
      apply: hM1ne; rewrite hM1; apply/eqP; rewrite -[_ == _]negbK -has_filter.
      apply/hasPn=> x hx; rewrite -leNgt -heq -hat.
      by have /andP[] := hbounds x hx.
    have hM1head : head 0 M1 = t.
      have hMne : M <> [::] by move=> h; rewrite h in htM.
      have hhd : head 0 M < t' by rewrite hhead hat.
      by rewrite hM1 (filter_lt_head hMne hhd) hhead hat.
    have hM1mem : forall x, x \in M1 -> t <= x <= t'.
      move=> x; rewrite hM1 mem_filter=> /andP[hxt' hxM].
      by rewrite (ltW hxt') andbT -hat; have /andP[] := hbounds x hxM.
    have hud : forall s, t <= s <= t' -> `|u - s| <= d.
      by move=> s /andP[h1 h2]; rewrite ler_distl; apply/andP; split; lra.
    have hin : forall s, t <= s <= t' -> a <= s <= b.
      by move=> s /andP[h1 h2]; rewrite hat h1 /=; exact: le_trans h2 ht'b.
    have huin : t <= u <= t' by rewrite htu hut'.
    have hall : forall s, s \in rcons M1 t' -> `|f u - f s| <= om.
      move=> s; rewrite mem_rcons inE=> /orP[/eqP->|hs].
      - by apply: hom (hin _ huin) (hin _ _) (hud _ _); rewrite (le_trans htu hut') lexx.
      - by apply: hom (hin _ huin) (hin _ (hM1mem _ hs)) (hud _ (hM1mem _ hs)).
    have hrcne : rcons M1 t' <> [::] by move=> h; have := size_rcons M1 t'; rewrite h.
    have hcell := cell_left_estimate hrcne hall.
    rewrite last_rcons (head_rcons_nonempty 0 t' hM1ne) hM1head in hcell.
    have hL : left_sum M = left_sum (rcons M1 t') + left_sum M2.
      by rewrite hsplit (left_sum_cat hM1ne hM2ne) (left_sum_rcons t' hM1ne) hM2head.
    have hAC : absolute_chain M = absolute_chain (rcons M1 t') + absolute_chain M2.
      by rewrite hsplit (absolute_chain_cat hM1ne hM2ne) (absolute_chain_rcons t' hM1ne) hM2head.
    rewrite stieltjes_sum_cons hL hAC.
    have -> : f u * (g t' - g t) + stieltjes_sum (t' :: rest') - (left_sum (rcons M1 t') + left_sum M2)
      = (f u * (g t' - g t) - left_sum (rcons M1 t')) + (stieltjes_sum (t' :: rest') - left_sum M2) by ring.
    apply: le_trans (ler_normD _ _) _; rewrite (mulrDr om); exact: lerD hcell hih.
Qed.

(** Source for [tagged_pair_estimate]: two Riemann-Stieltjes sums with
    mesh below delta differ by at most
    2 sup{|f(u) - f(v)| : |u - v| <= delta} times the absolute increment
    sum over a nondecreasing list from a to b, the diameter estimate of
    Federer 2.5.17, p. 111, with the common refinement made explicit. *)
Theorem tagged_pair_estimate (a b d om : R) (w w' : seq R) :
  is_tagged_partition a b w -> is_tagged_partition a b w' ->
  tagged_mesh_lt d w -> tagged_mesh_lt d w' ->
  (forall x y, a <= x <= b -> a <= y <= b -> `|x - y| <= d -> `|f x - f y| <= om) ->
  exists M : seq R, sorted <=%O M /\ head 0 M = a /\ last 0 M = b /\
    `|stieltjes_sum w - stieltjes_sum w'| <= 2 * om * absolute_chain M.
Proof.
move=> hw hw' hm hm' hom.
pose M := merge <=%O (tagged_points w) (tagged_points w').
have hM : sorted <=%O M.
  exact (merge_sorted le_total (tagged_points_sorted hw.1) (tagged_points_sorted hw'.1)).
have hmemM : forall x, (x \in M) = (x \in tagged_points w) || (x \in tagged_points w').
  by move=> x; rewrite /M mem_merge mem_cat.
have hbounds : forall x, x \in M -> a <= x <= b.
  move=> x; rewrite hmemM=> /orP[hx|hx].
  - exact (tagged_partition_points_bounds hw hx).
  - exact (tagged_partition_points_bounds hw' hx).
have ha : a \in M by rewrite hmemM (tagged_partition_a_mem hw).
have hb : b \in M by rewrite hmemM (tagged_partition_b_mem hw).
have hhead : head 0 M = a.
  by apply: sorted_head_eq=> // x hx; have /andP[] := hbounds x hx.
have hlast : last 0 M = b.
  by apply: sorted_last_eq=> // x hx; have /andP[_] := hbounds x hx.
have hsub : {subset tagged_points w <= M} by move=> x hx; rewrite hmemM hx.
have hsub' : {subset tagged_points w' <= M} by move=> x hx; rewrite hmemM hx orbT.
exists M; split=> //; split=> //; split=> //.
have h1 := tagged_refinement_estimate hw hm hM hsub hhead hlast hom.
have h2 := tagged_refinement_estimate hw' hm' hM hsub' hhead hlast hom.
apply: le_trans (ler_distD (left_sum M) _ _) _.
have -> : 2 * om * absolute_chain M = om * absolute_chain M + om * absolute_chain M by ring.
by apply: lerD=> //; rewrite distrC.
Qed.

End StieltjesSums.
