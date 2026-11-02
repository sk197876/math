(** Federer (1969), 2.5.16, p. 109: the variation (or length) V_a^b g of a
    map g from R into a metric space Y, defined as the supremum of the sums
    of the distances rho[g(t_i),g(t_(i+1))] over all finite sequences
    a=t_1<=t_2<=...<=t_(n+1)=b, and the identity V_a^b g+V_b^c g=V_a^c g for
    a<=b<=c. Finite sequences are represented by sorted lists with first
    term a and last term b and at least two terms. The supremum uses the
    project's sealed extended bounds of 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sorted_head_le]: supporting order fact for the finite
    sequences in Federer 2.5.16, p. 109: every term is at least the
    first term. *)
Lemma sorted_head_le (R : realType) (s : seq R) (a x : R) :
  sorted <=%O s -> x \in s -> (head a s <= x)%R.
Proof.
case: s=> [//|t s'] /= hs; rewrite inE=> /orP[/eqP->//|hx].
by have := order_path_min le_trans hs; move/allP; exact.
Qed.

(** Source for [sorted_le_last]: supporting order fact for the finite
    sequences in Federer 2.5.16, p. 109: every term is at most the
    last term. *)
Lemma sorted_le_last (R : realType) (s : seq R) (a x : R) :
  sorted <=%O s -> x \in s -> (x <= last a s)%R.
Proof.
elim: s a=> [//|t s' ih] a /=; rewrite (path_sortedE le_trans)=> /andP[hall hs'].
rewrite inE=> /orP[/eqP->|hx]; last exact: ih.
case: s' hall {hs' ih}=> [|u s''] hall; first by rewrite /= lexx.
have := allP hall _ (mem_last u s'').
by rewrite /=.
Qed.

(** Source for [sorted_cat_le]: supporting concatenation of two sorted
    sequences when every term of the first is at most every term of the
    second, Federer 2.5.16, p. 109. *)
Lemma sorted_cat_le (R : realType) (s1 s2 : seq R) :
  sorted <=%O s1 -> sorted <=%O s2 ->
  (forall x y, x \in s1 -> y \in s2 -> (x <= y)%R) -> sorted <=%O (s1 ++ s2).
Proof.
elim: s1=> [//|t s1 ih] /=; rewrite !(path_sortedE le_trans)=> /andP[hall hs1] hs2 hle.
apply/andP; split.
- rewrite all_cat hall /=; apply/allP=> y hy; apply: hle=> //.
  by rewrite inE eqxx.
- apply: ih=> // x y hx hy; apply: hle=> //.
  by rewrite inE hx orbT.
Qed.

(** Source for [sorted_split_filter]: supporting decomposition of a
    sorted sequence at a threshold, used to insert the point b in the
    proof of V_a^b g+V_b^c g=V_a^c g, Federer 2.5.16, p. 109. *)
Lemma sorted_split_filter (R : realType) (s : seq R) (b : R) :
  sorted <=%O s -> s = [seq x <- s | (x < b)%R] ++ [seq x <- s | (b <= x)%R].
Proof.
elim: s=> [//|t s ih] /=; rewrite (path_sortedE le_trans)=> /andP[hall hs].
case: (ltP t b)=> htb /=.
- by rewrite -(ih hs).
- have h1 : [seq x <- s | (x < b)%R] = [::].
    apply/eqP; rewrite -[_ == _]negbK -has_filter; apply/hasPn=> x hx.
    by rewrite -leNgt; apply: le_trans htb _; exact: (allP hall).
  have h2 : [seq x <- s | (b <= x)%R] = s.
    by apply/all_filterP/allP=> x hx; apply: le_trans htb _; exact: (allP hall).
  by rewrite h1 h2.
Qed.

Section Variation.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.

(** Source for [chain_sum]: the sum of the distances
    rho[g(t_i),g(t_(i+1))] along a finite sequence t_1,...,t_(n+1) in
    Federer 2.5.16, p. 109. A sequence with at most one term has
    sum zero. *)
Fixpoint chain_sum (s : seq R) : R :=
  match s with
  | t :: ((u :: _) as rest) => (mdist (g t) (g u) + chain_sum rest)%R
  | _ => 0%R
  end.

(** Source for [is_variation_partition]: a finite sequence
    a=t_1<=t_2<=...<=t_(n+1)=b with n>=1 in Federer 2.5.16, p. 109. *)
Definition is_variation_partition (a b : R) (s : seq R) : Prop :=
  sorted <=%O s /\ (1 < size s)%N /\ head a s = a /\ last a s = b.

(** Source for [variation_sums]: the set of numbers whose supremum
    defines V_a^b g in Federer 2.5.16, p. 109. *)
Definition variation_sums (a b : R) : set (\bar R) :=
  [set v | exists s, is_variation_partition a b s /\ v = (chain_sum s)%:E].

(** Source for [curve_variation]: direct definition of V_a^b g for
    a<=b in Federer 2.5.16, p. 109, as the supremum of the sums. *)
Definition curve_variation (a b : R) : \bar R := extended_real_sup (variation_sums a b).

(** Source for [signed_curve_variation]: the convention V_a^b g=-V_b^a g
    for a>b in Federer 2.5.16, p. 109. *)
Definition signed_curve_variation (a b : R) : \bar R :=
  if (a <= b)%R then curve_variation a b else - curve_variation b a.

(** Source for [chain_sum_nonnegative]: supporting nonnegativity of
    the sums in Federer 2.5.16, p. 109. *)
Lemma chain_sum_nonnegative (s : seq R) : (0 <= chain_sum s)%R.
Proof.
elim: s=> [|t [|u rest] ih] //=.
by apply: addr_ge0=> //; exact: mdist_ge0.
Qed.

(** Source for [chain_sum_cat]: supporting concatenation formula for
    the sums in Federer 2.5.16, p. 109: the junction contributes the
    distance between the last term of the first sequence and the first
    term of the second. *)
Lemma chain_sum_cons (t u : R) (s : seq R) :
  chain_sum (t :: u :: s) = (mdist (g t) (g u) + chain_sum (u :: s))%R.
Proof. by []. Qed.

Lemma chain_sum_cat (s1 s2 : seq R) :
  s1 <> [::] -> s2 <> [::] ->
  chain_sum (s1 ++ s2) =
    (chain_sum s1 + mdist (g (last 0 s1)) (g (head 0 s2)) + chain_sum s2)%R.
Proof.
elim: s1=> [//|t [|u rest] ih _ hs2].
- by case: s2 hs2 {ih}=> [//|v s2' _] /=; rewrite add0r.
- have hne : u :: rest <> [::] by [].
  rewrite !cat_cons chain_sum_cons -[u :: rest ++ s2]cat_cons (ih hne hs2).
  by rewrite [in RHS]chain_sum_cons !addrA.
Qed.

(** Source for [chain_sum_rcons]: supporting formula for appending a
    final term, Federer 2.5.16, p. 109. *)
Lemma chain_sum_rcons (s : seq R) (b : R) :
  s <> [::] -> chain_sum (rcons s b) = (chain_sum s + mdist (g (last 0 s)) (g b))%R.
Proof. by move=> hs; rewrite -cats1 (chain_sum_cat hs) //= addr0. Qed.

(** Source for [chain_sum_junction_bound]: supporting triangle
    inequality for inserting an intermediate point in Federer 2.5.16,
    p. 109: the sum over a sequence is at most the sum after inserting
    b between the two parts. *)
Lemma chain_sum_junction_bound (s1 s2 : seq R) (b : R) :
  s1 <> [::] -> s2 <> [::] ->
  (chain_sum (s1 ++ s2) <= chain_sum (rcons s1 b) + chain_sum (b :: s2))%R.
Proof.
move=> h1 h2; rewrite (chain_sum_cat h1 h2) (chain_sum_rcons _ h1).
case: s2 h2=> [//|v s2' _] /=.
rewrite -!addrA lerD2l addrA lerD2r.
exact: metric_triangle.
Qed.

(** Source for [chain_sum_constant]: a constant sequence has sum zero,
    the degenerate case a=b of Federer 2.5.16, p. 109. *)
Lemma chain_sum_constant (s : seq R) (a : R) :
  (forall x, x \in s -> x = a) -> chain_sum s = 0%R.
Proof.
elim: s=> [//|t [|u rest] ih] //= hall.
have ht : t = a by apply: hall; rewrite inE eqxx.
have hu : u = a by apply: hall; rewrite !inE eqxx orbT.
have -> : mdist (g t) (g u) = 0%R by rewrite ht hu mdistxx.
by rewrite add0r; apply: ih=> x hx; apply: hall; rewrite inE hx orbT.
Qed.

(** Source for [variation_partition_bounds]: every term of a sequence
    a=t_1<=...<=t_(n+1)=b lies between a and b, Federer 2.5.16, p. 109. *)
Lemma variation_partition_bounds (a b : R) (s : seq R) :
  is_variation_partition a b s -> forall x, x \in s -> (a <= x <= b)%R.
Proof.
move=> [hs [hn [hh hl]]] x hx; apply/andP; split.
- by rewrite -hh; exact: sorted_head_le hs hx.
- by rewrite -hl; exact: sorted_le_last hs hx.
Qed.

(** Source for [variation_partition_pair]: the two-term sequence a,b
    in Federer 2.5.16, p. 109. *)
Lemma variation_partition_pair (a b : R) : (a <= b)%R -> is_variation_partition a b [:: a; b].
Proof. by move=> hab; split; [rewrite /= andbT|]. Qed.

(** Source for [curve_variation_ge_distance]: rho[g(a),g(b)] <= V_a^b g,
    the two-term sequence in Federer 2.5.16, p. 109. *)
Lemma curve_variation_ge_distance (a b : R) :
  (a <= b)%R -> (mdist (g a) (g b))%:E <= curve_variation a b.
Proof.
move=> hab; apply: extended_real_sup_upper; exists [:: a; b].
by split; [exact: variation_partition_pair|rewrite /= addr0].
Qed.

(** Source for [curve_variation_nonnegative]: V_a^b g >= 0 for a<=b,
    Federer 2.5.16, p. 109. *)
Lemma curve_variation_nonnegative (a b : R) : (a <= b)%R -> 0 <= curve_variation a b.
Proof.
move=> hab; apply: le_trans (curve_variation_ge_distance hab).
by rewrite lee_fin; exact: mdist_ge0.
Qed.

(** Source for [curve_variation_self]: V_a^a g=0, the degenerate case
    of Federer 2.5.16, p. 109: every sequence from a to a is constant. *)
Lemma curve_variation_self (a : R) : curve_variation a a = 0.
Proof.
apply/le_anti/andP; split; last exact: curve_variation_nonnegative.
apply: extended_real_sup_least=> v [s [hs ->]]; rewrite lee_fin.
rewrite (chain_sum_constant (a := a)) // => x hx.
by have /andP[h1 h2] := variation_partition_bounds hs hx; apply: le_anti; rewrite h1 h2.
Qed.

(** Source for [curve_variation_sum_upper]: supporting lower estimate
    of V_a^c g by the sums over concatenated sequences from a to b and
    from b to c, Federer 2.5.16, p. 109. *)
Lemma curve_variation_sum_upper (a b c : R) (s1 s2 : seq R) :
  is_variation_partition a b s1 -> is_variation_partition b c s2 ->
  (chain_sum s1 + chain_sum s2)%R%:E <= curve_variation a c.
Proof.
move=> [hs1 [hn1 [hh1 hl1]]] [hs2 [hn2 [hh2 hl2]]].
case: s2 hs2 hn2 hh2 hl2=> [//|t [//|u s2']] hs2 _ /= hh2 hl2.
have h1 : s1 <> [::] by case: s1 hn1 hs1 hh1 hl1.
apply: extended_real_sup_upper; exists (s1 ++ u :: s2'); split.
- split.
  + apply: sorted_cat_le=> //; first by move: hs2; rewrite /= => /andP[].
    move=> x y hx hy; apply: le_trans (sorted_le_last a hs1 hx) _.
    rewrite hl1 -hh2; have := order_path_min le_trans hs2.
    by move/allP; exact.
  + split; first by rewrite size_cat /= addnS ltnS; exact: leq_trans (ltnW hn1) (leq_addr _ _).
    split; first by case: s1 hh1 h1 hs1 hn1 hl1=> [//|x s1'] /= -> *.
    by rewrite last_cat /= -hl2.
- have hl0 : last 0%R s1 = t.
    by rewrite hh2 -hl1; case: s1 h1 hs1 hn1 hh1 hl1.
  by rewrite (chain_sum_cat h1) //= hl0 addrA.
Qed.

(** Source for [extended_sup_approximation]: supporting approximation
    of a finite supremum from below, Federer 2.1.1, p. 51, used in
    the proof of V_a^b g+V_b^c g=V_a^c g, 2.5.16, p. 109. *)
Lemma extended_sup_approximation (S : set (\bar R)) (a e : R) :
  extended_real_sup S = a%:E -> (0 < e)%R -> exists x, S x /\ (a - e)%:E < x.
Proof.
move=> hS he; apply: contrapT=> hn.
have hub : extended_real_sup S <= (a - e)%:E.
  apply: extended_real_sup_least=> x hx; rewrite leNgt; apply/negP=> hlt.
  by apply: hn; exists x.
move: hub; rewrite hS lee_fin leNgt=> /negP; apply.
by rewrite ltrBlDr ltrDl.
Qed.

(** Source for [extended_sup_sum_bound]: supporting inequality
    sup S_1+sup S_2 <= V when every pair of finite members sums to at
    most V, Federer 2.1.1, p. 51, used for V_a^b g+V_b^c g <= V_a^c g
    in 2.5.16, p. 109. *)
Lemma extended_sup_sum_bound (S1 S2 : set (\bar R)) (V : \bar R) :
  (exists x, S1 x) -> (exists y, S2 y) ->
  (forall x, S1 x -> exists r : R, x = r%:E) -> (forall y, S2 y -> exists r : R, y = r%:E) ->
  (forall x y, S1 x -> S2 y -> x + y <= V) ->
  extended_real_sup S1 + extended_real_sup S2 <= V.
Proof.
move=> [x0 hx0] [y0 hy0] hf1 hf2 hV.
case: (pselect (V = +oo))=> [->|hVinf]; first exact: leey.
have [r0 hr0] := hf1 x0 hx0; have [q0 hq0] := hf2 y0 hy0.
have hVfin : exists v : R, V = v%:E.
  have := hV x0 y0 hx0 hy0; rewrite hr0 hq0 -EFinD; clear hV.
  by case: V hVinf=> [v _ _|//|_ h]; [exists v|rewrite leeNy_eq in h].
have [v hv] := hVfin; rewrite hv.
have hS1 : extended_real_sup S1 <> -oo.
  by move=> h; have := extended_real_sup_upper hx0; rewrite h hr0 leeNy_eq.
have hS2 : extended_real_sup S2 <> -oo.
  by move=> h; have := extended_real_sup_upper hy0; rewrite h hq0 leeNy_eq.
have hbound1 : forall y, S2 y -> extended_real_sup S1 <= V - y.
  move=> y hy; have [q hq] := hf2 y hy.
  apply: extended_real_sup_least=> x hx; have [r hr] := hf1 x hx.
  have := hV x y hx hy; rewrite hr hq hv -EFinD lee_fin -lerBrDr=> h.
  by rewrite -EFinB lee_fin.
have hbound2 : forall x, S1 x -> extended_real_sup S2 <= V - x.
  move=> x hx; have [r hr] := hf1 x hx.
  apply: extended_real_sup_least=> y hy; have [q hq] := hf2 y hy.
  have := hV x y hx hy; rewrite hr hq hv -EFinD lee_fin -lerBrDl=> h.
  by rewrite -EFinB lee_fin.
have [a Ea] : exists a : R, extended_real_sup S1 = a%:E.
  have := hbound1 y0 hy0; rewrite hv hq0 -EFinB.
  case: (extended_real_sup S1) hS1=> [a _ _|_ h|h _].
  - by exists a.
  - by rewrite leye_eq in h.
  - by case: (h erefl).
have [b Eb] : exists b : R, extended_real_sup S2 = b%:E.
  have := hbound2 x0 hx0; rewrite hv hr0 -EFinB.
  case: (extended_real_sup S2) hS2=> [b _ _|_ h|h _].
  - by exists b.
  - by rewrite leye_eq in h.
  - by case: (h erefl).
rewrite Ea Eb -EFinD lee_fin leNgt; apply/negP=> hlt.
pose e := ((a + b - v) / 2%:R)%R.
have he : (0 < e)%R by rewrite divr_gt0 ?subr_gt0 ?ltr0n.
have [x [hx hax]] := extended_sup_approximation Ea he.
have [y [hy hby]] := extended_sup_approximation Eb he.
have [r hr] := hf1 x hx; have [q hq] := hf2 y hy.
have := hV x y hx hy; rewrite hr hq hv -EFinD lee_fin leNgt=> /negP; apply.
move: hax hby; rewrite hr hq !lte_fin=> hax hby.
have : (a - e + (b - e) < r + q)%R by exact: ltrD.
apply: le_lt_trans; rewrite /e.
by rewrite addrACA -opprD -splitr opprB addrC subrK.
Qed.

(** Source for [curve_variation_split]: the identity
    V_a^b g+V_b^c g=V_a^c g for a<=b<=c in Federer 2.5.16, p. 109.
    Concatenating sequences gives one inequality; inserting the point b
    into a sequence from a to c and the triangle inequality give the other. *)
Theorem curve_variation_split (a b c : R) : (a <= b)%R -> (b <= c)%R ->
  curve_variation a c = curve_variation a b + curve_variation b c.
Proof.
move=> hab hbc; apply/le_anti/andP; split; last first.
- apply: extended_sup_sum_bound.
  + exists (chain_sum [:: a; b])%:E, [:: a; b]; split=> //.
    exact: variation_partition_pair.
  + exists (chain_sum [:: b; c])%:E, [:: b; c]; split=> //.
    exact: variation_partition_pair.
  + by move=> x [s [_ ->]]; exists (chain_sum s).
  + by move=> y [s [_ ->]]; exists (chain_sum s).
  + move=> x y [s1 [hs1 ->]] [s2 [hs2 ->]]; rewrite -EFinD.
    exact: curve_variation_sum_upper hs1 hs2.
- case: (pselect (a = b))=> [<-|hne]; first by rewrite curve_variation_self add0e.
  have hab' : (a < b)%R by rewrite lt_neqAle hab andbT; apply/eqP.
  apply: extended_real_sup_least=> v [s [hs ->]].
  have [hsort [hn [hh hl]]] := hs.
  have ha_s : a \in s by case: s hh hn hs hsort hl=> [//|t s'] /= -> _ _ _ _; exact: mem_head.
  have hc_s : c \in s by rewrite -hl; case: s hn hs hsort hh hl ha_s=> [//|t s'] _ _ _ _ _ _ /=; exact: mem_last.
  have [s_low hs_low] : exists s_low, s_low = [seq x <- s | (x < b)%R] by eexists.
  have [s_high hs_high] : exists s_high, s_high = [seq x <- s | (b <= x)%R] by eexists.
  have hsplit : s = s_low ++ s_high by rewrite hs_low hs_high; exact: sorted_split_filter.
  have hlow : s_low <> [::].
    move=> h; have : a \in s_low by rewrite hs_low mem_filter hab' ha_s.
    by rewrite h.
  have hhigh : s_high <> [::].
    move=> h; have : c \in s_high by rewrite hs_high mem_filter hbc hc_s.
    by rewrite h.
  have hlow_sorted : sorted <=%O s_low.
    by rewrite hs_low; exact (sorted_filter le_trans _ hsort).
  have hhigh_sorted : sorted <=%O s_high.
    by rewrite hs_high; exact (sorted_filter le_trans _ hsort).
  have hhead_low : head a s_low = a.
    move: hh; rewrite {1}hsplit.
    by case: s_low hlow {hs_low hsplit hlow_sorted}=> [//|t l] _ /= ->.
  have hp1 : is_variation_partition a b (rcons s_low b).
    split.
    - rewrite -cats1; apply: sorted_cat_le=> // x y hx; rewrite inE=> /eqP->.
      by move: hx; rewrite hs_low mem_filter=> /andP[hxb _]; exact: ltW hxb.
    - split; first by rewrite size_rcons ltnS lt0n size_eq0; apply/eqP.
      split; last by rewrite last_rcons.
      by case: s_low hlow hhead_low {hs_low hsplit hlow_sorted}=> [//|t l] _ /= ->.
  have hp2 : is_variation_partition b c (b :: s_high).
    split.
    - rewrite /= (path_sortedE le_trans) hhigh_sorted andbT.
      by apply/allP=> x; rewrite hs_high mem_filter=> /andP[].
    - split; first by rewrite /= ltnS lt0n size_eq0; apply/eqP.
      split=> //.
      move: hl; rewrite {1}hsplit last_cat.
      by case: s_high hhigh {hs_high hsplit hhigh_sorted}=> [//|t l] _ /= ->.
  have hbound : (chain_sum s <= chain_sum (rcons s_low b) + chain_sum (b :: s_high))%R.
    by rewrite {1}hsplit; exact: chain_sum_junction_bound.
  have hfin : (chain_sum s)%:E <= (chain_sum (rcons s_low b))%:E + (chain_sum (b :: s_high))%:E.
    by rewrite -EFinD lee_fin.
  apply: le_trans hfin _; apply: leeD; apply: extended_real_sup_upper.
  + by exists (rcons s_low b).
  + by exists (b :: s_high).
Qed.

(** Source for [curve_variation_monotone]: V_a'^b' g <= V_a^b g for
    a<=a'<=b'<=b, a consequence of the additivity in Federer 2.5.16,
    p. 109, and nonnegativity. *)
Lemma curve_variation_monotone (a a' b' b : R) :
  (a <= a')%R -> (a' <= b')%R -> (b' <= b)%R -> curve_variation a' b' <= curve_variation a b.
Proof.
move=> h1 h2 h3.
rewrite (curve_variation_split h1 (le_trans h2 h3)) (curve_variation_split h2 h3) addeA.
apply: lee_paddr (curve_variation_nonnegative h3) _.
exact: lee_paddl (curve_variation_nonnegative h1) (lexx _).
Qed.

End Variation.
