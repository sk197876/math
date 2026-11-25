(** Federer (1969), 2.7.4, printed pp. 123-124: "Obviously C(u,v) <> empty
    and (u:v) >= sup im u/sup im v, (u o A_h:v) = (u:v) for h in G, (cu:v) =
    c(u:v) for 0 < c < oo, (u_1+u_2:v) <= (u_1:v)+(u_2:v), u_1 <= u_2
    implies (u_1:v) <= (u_2:v). Moreover, if u, v, w in K(X)+ are nonzero,
    then (u:w) <= (u:v).(v:w) because xi in C(u,v) and eta in C(v,w) implies
    u <= sum_{g in G} xi(g) sum_{h in G} eta(h)(w o A_h o A_g) = sum_{k in
    G} zeta(k)(w o A_k) with zeta(k) = sum_{hg=k} xi(g) eta(h), sum_G zeta =
    sum_G xi . sum_G eta. Consequently 1/(w:u) <= (u:v)/(w:v) <= (u:w)."
    Federer gives no further proof of the first list. The Haar ratio is
    specified in HaarRatioUP.v. A member xi of C(u,v) corresponds to the
    finite family of the pairs (g, xi(g)) with xi(g) > 0, and every finite
    family (g_i, c_i) with c_i >= 0 and u <= sum_i c_i (v o A_{g_i}) yields
    the member g |-> sum_{g_i = g} c_i of C(u,v) with the same sum
    (haar_cover_family, haar_family_cover_function). The properties are
    proved for such families; for (u:w) <= (u:v).(v:w) the composite family
    consists of the pairs (hg, xi(g) eta(h)), and the map it determines is
    Federer's zeta. For the nonemptiness of C(u,v), choose b with v(b) > 0
    and, for each x in X, some g_x with A(g_x,x) = b; the open sets {x:
    v(A(g_x,x)) > v(b)/2} cover the compact set spt u, and finitely many of
    them suffice. The infimum exists because C(u,v) is nonempty. Federer
    assumes u, v, w nonzero for (u:w) <= (u:v).(v:w); the proof uses only
    that v and w are nonzero, and so does the right inequality of the last
    display, while the left inequality needs nonzero u. The definition of a
    homogeneous space (2.7.1, p. 121) is used for the nonemptiness and for
    A_{hg} = A_h o A_g, and the group laws for (u o A_h:v) = (u:v); neither
    local compactness nor the Hausdorff property of X or G is needed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  cardinality fsbigop topology.
From mathcomp.analysis.normedtype_theory Require Import num_normedtype.
From mathcomp Require Import lra.
From Federer Require Import FunctionLatticeUP CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactMaximum CompactFiniteCover TopologicalGroupUP
  HomogeneousSpaceUP HomogeneousSpaceLaws CovariantIntegralLaws HaarRatioUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarFamilies.
Variable R : realType.
Variable G : choiceType.
Variable X : topologicalType.
Variable A : G -> X -> X.
Implicit Types (u v w : X -> R) (r b c eps : R) (s t : seq (G * R)).

(** Source for [haar_family_cover]: the condition "u <= sum_{g in G}
    xi(g) . (v o A_g)" of Federer 2.7.4, p. 123, for a finite family of
    pairs (g, xi(g)) with nonnegative second members. Supporting
    definition; haar_cover_family and haar_family_cover_function relate
    it to C(u,v). *)
Definition haar_family_cover (u v : X -> R) (s : seq (G * R)) : Prop :=
  (forall p, p \in s -> 0 <= p.2) /\ function_le u (fun x => \sum_(p <- s) p.2 * v (A p.1 x)).

(** Source for [haar_family_total]: the sum "sum_G xi" of Federer
    2.7.4, p. 123, for a finite family of pairs (g, xi(g)). Supporting
    definition. *)
Definition haar_family_total (s : seq (G * R)) : R := \sum_(p <- s) p.2.

(** Source for [group_sum_seq]: a finitely supported sum over G, as in
    "sum_{g in G} xi(g) . (v o A_g)" of Federer 2.7.4, p. 123, is the
    sum over any duplicate-free list containing the support. Supporting
    lemma. *)
Lemma group_sum_seq (H : G -> R) (r : seq G) : uniq r -> (forall g, g \notin r -> H g = 0) ->
  \sum_(g \in [set: G]) H g = \sum_(g <- r) H g.
Proof.
move=> hr h0; rewrite [RHS]fsbig_seq // (fsbig_widen [set` r] [set: G] H) //.
by move=> g [_ hg]; apply: h0; apply/negP.
Qed.

(** Source for [family_function]: the map g |-> sum_{g_i = g} c_i
    determined by a finite family (g_i, c_i), as zeta(k) =
    sum_{hg=k} xi(g) eta(h) in Federer 2.7.4, p. 124. Supporting
    definition. *)
Definition family_function (s : seq (G * R)) : G -> R := fun g => \sum_(p <- s | p.1 == g) p.2.

(** Source for [family_function_sum]: the regrouping
    sum_k zeta(k) F(k) = sum_i c_i F(g_i) used in Federer 2.7.4, p. 124.
    Supporting lemma. *)
Lemma family_function_sum (s : seq (G * R)) (F : G -> R) :
  \sum_(g <- undup (map fst s)) family_function s g * F g = \sum_(p <- s) p.2 * F p.1.
Proof.
rewrite /family_function.
under eq_bigr do rewrite mulr_suml.
rewrite (exchange_big_dep xpredT) //= big_seq [RHS]big_seq; apply: eq_bigr=> p hp.
have hu : uniq (undup (map fst s)) := undup_uniq _.
have hin : p.1 \in undup (map fst s) by rewrite mem_undup; apply: map_f.
rewrite (eq_bigl (pred1 p.1)); last by move=> g; rewrite /= eq_sym.
by rewrite -big_filter filter_pred1_uniq // big_seq1.
Qed.

(** Source for [family_function_zero]: the map determined by a finite
    family vanishes off the first members, supporting the finiteness of
    {g: xi(g) > 0} in Federer 2.7.4, p. 123. *)
Lemma family_function_zero (s : seq (G * R)) g : g \notin undup (map fst s) -> family_function s g = 0.
Proof.
rewrite mem_undup=> hg; rewrite /family_function big_seq_cond big1 // => p /andP [hp /eqP hpg].
by move: hg; rewrite -hpg map_f.
Qed.

(** Source for [family_function_nonneg]: "xi: G -> {t: 0 <= t < oo}",
    Federer 2.7.4, p. 123, for the map determined by a family with
    nonnegative members. Supporting lemma. *)
Lemma family_function_nonneg (s : seq (G * R)) : (forall p, p \in s -> 0 <= p.2) ->
  forall g, 0 <= family_function s g.
Proof.
move=> hs g; rewrite /family_function big_seq_cond; apply: sumr_ge0=> p /andP [hp _]; exact: hs.
Qed.

(** Source for [haar_cover_family]: every xi in C(u,v), Federer 2.7.4,
    p. 123, is given by the finite family of the pairs (g, xi(g)) with
    xi(g) > 0, with the same sum. Supporting lemma. *)
Lemma haar_cover_family u v xi : haar_cover A u v xi ->
  exists s, haar_family_cover u v s /\ haar_family_total s = group_sum xi.
Proof.
case=> h0 hfin hle.
pose r := fset_set [set g | 0 < xi g].
have hr : uniq r := fset_uniq _.
have hsupp g : g \notin r -> xi g = 0.
  rewrite in_fset_set // notin_setE /= => hg.
  by apply/eqP; rewrite eq_le h0 andbT leNgt; apply/negP.
exists [seq (g, xi g) | g <- r]; split; [split|].
- by move=> p /mapP [g _ ->]; exact: h0.
- move=> x; apply: le_trans (hle x) _; rewrite (group_sum_seq hr) ?big_map //.
  by move=> g /hsupp ->; rewrite mul0r.
- by rewrite /haar_family_total /group_sum big_map (group_sum_seq hr).
Qed.

(** Source for [haar_family_cover_function]: every finite family
    (g_i, c_i) with c_i >= 0 and u <= sum_i c_i (v o A_{g_i}) yields a
    member g |-> sum_{g_i = g} c_i of C(u,v), Federer 2.7.4, p. 123, with
    the same sum, as zeta in Federer 2.7.4, p. 124. Supporting lemma. *)
Lemma haar_family_cover_function u v s : haar_family_cover u v s ->
  haar_cover A u v (family_function s) /\ group_sum (family_function s) = haar_family_total s.
Proof.
case=> hs hle.
have hu : uniq (undup (map fst s)) := undup_uniq _.
have hz g : g \notin undup (map fst s) -> family_function s g = 0 := @family_function_zero s g.
split; [split|].
- exact: family_function_nonneg.
- apply: (sub_finite_set _ (finite_seq (undup (map fst s))))=> g /= hg.
  apply: contrapT=> /negP /hz hg0; by move: hg; rewrite hg0 ltxx.
- move=> x; rewrite (group_sum_seq hu); first by rewrite family_function_sum; exact: hle.
  by move=> g /hz ->; rewrite mul0r.
- rewrite /group_sum (group_sum_seq hu) //.
  have := family_function_sum s (fun _ => 1).
  under eq_bigr do rewrite mulr1.
  by move=> ->; rewrite /haar_family_total; apply: eq_bigr=> p _; rewrite mulr1.
Qed.

(** Source for [is_haar_ratioP]: "(u:v) = inf{sum_G xi: xi in
    C(u,v)}", Federer 2.7.4, p. 123, expressed through finite families.
    Supporting characterisation. *)
Lemma is_haar_ratioP u v r : is_haar_ratio A u v r <->
  (forall s, haar_family_cover u v s -> r <= haar_family_total s) /\
  (forall b, (forall s, haar_family_cover u v s -> b <= haar_family_total s) -> b <= r).
Proof.
split=> [[hlow hglb]|[hlow hglb]]; split.
- by move=> s hs; have [hxi <-] := haar_family_cover_function hs; exact: hlow.
- move=> b hb; apply: hglb=> xi hxi; have [s [hs <-]] := haar_cover_family hxi; exact: hb.
- by move=> xi hxi; have [s [hs <-]] := haar_cover_family hxi; exact: hlow.
- move=> b hb; apply: hglb=> s hs; have [hxi <-] := haar_family_cover_function hs; exact: hb.
Qed.

(** Source for [haar_family_total_nonneg]: "xi: G -> {t: 0 <= t < oo}",
    Federer 2.7.4, p. 123: the sums are nonnegative. Supporting lemma. *)
Lemma haar_family_total_nonneg u v s : haar_family_cover u v s -> 0 <= haar_family_total s.
Proof. by case=> hs _; rewrite /haar_family_total big_seq; apply: sumr_ge0=> p; exact: hs. Qed.

(** Source for [haar_ratio_lower]: the Haar ratio is a lower bound of
    the sums, Federer 2.7.4, p. 123. Supporting lemma. *)
Lemma haar_ratio_lower u v r s : is_haar_ratio A u v r -> haar_family_cover u v s ->
  r <= haar_family_total s.
Proof. by move=> /is_haar_ratioP [h _]; exact: h. Qed.

(** Source for [haar_ratio_approx]: the Haar ratio is approximated
    by the sums, as an infimum, Federer 2.7.4, p. 123. Supporting
    lemma. *)
Lemma haar_ratio_approx u v r eps : is_haar_ratio A u v r -> 0 < eps ->
  exists2 s, haar_family_cover u v s & haar_family_total s < r + eps.
Proof.
move=> /is_haar_ratioP [_ hglb] he; apply: contrapT=> hno.
have : r + eps <= r.
  apply: hglb=> s hs; rewrite leNgt; apply/negP=> hlt; apply: hno; by exists s.
by move=> h; lra.
Qed.

(** Source for [haar_ratio_nonneg]: (u:v) >= 0, from
    "xi: G -> {t: 0 <= t < oo}", Federer 2.7.4, p. 123. Supporting
    lemma. *)
Lemma haar_ratio_nonneg u v r : is_haar_ratio A u v r -> 0 <= r.
Proof. by move=> /is_haar_ratioP [_ hglb]; apply: hglb=> s; exact: haar_family_total_nonneg. Qed.

(** Source for [haar_ratio_unique]: the infimum "(u:v) = inf{...}" of
    Federer 2.7.4, p. 123, is unique. Supporting lemma. *)
Lemma haar_ratio_unique u v r r' : is_haar_ratio A u v r -> is_haar_ratio A u v r' -> r = r'.
Proof.
move=> [hl hg] [hl' hg']; apply/eqP; rewrite eq_le.
by rewrite (hg' _ hl) (hg _ hl').
Qed.

(** Source for [is_haar_ratio_transfer]: supporting lemma for the
    equalities (u o A_h:v) = (u:v) and (cu:v) = c(u:v) of Federer 2.7.4,
    p. 123: if the families for (u,v) and (u',v') correspond with totals
    multiplied by c > 0, then (u':v') = c (u:v). *)
Lemma is_haar_ratio_transfer u v u' v' r c : 0 < c -> is_haar_ratio A u v r ->
  (forall s, haar_family_cover u v s ->
    exists2 s', haar_family_cover u' v' s' & haar_family_total s' <= c * haar_family_total s) ->
  (forall s', haar_family_cover u' v' s' ->
    exists2 s, haar_family_cover u v s & c * haar_family_total s <= haar_family_total s') ->
  is_haar_ratio A u' v' (c * r).
Proof.
move=> hc /is_haar_ratioP [hlow hglb] h1 h2; apply/is_haar_ratioP; split.
- move=> s' hs'; have [s hs hle] := h2 _ hs'; apply: le_trans hle.
  by rewrite ler_pM2l //; exact: hlow.
- move=> b hb; rewrite -ler_pdivrMl //; apply: hglb=> s hs.
  have [s' hs' hle] := h1 _ hs; rewrite ler_pdivrMl //; exact: le_trans (hb _ hs') hle.
Qed.

(** Source for [haar_ratio_le_transfer]: supporting lemma for the
    inequalities of Federer 2.7.4, p. 123: if every family for (u,v)
    yields a family for (u',v') with total at most c times as large,
    c > 0, then (u':v') <= c (u:v). *)
Lemma haar_ratio_le_transfer u v u' v' r r' c : 0 < c -> is_haar_ratio A u v r ->
  is_haar_ratio A u' v' r' ->
  (forall s, haar_family_cover u v s ->
    exists2 s', haar_family_cover u' v' s' & haar_family_total s' <= c * haar_family_total s) ->
  r' <= c * r.
Proof.
move=> hc /is_haar_ratioP [_ hglb] /is_haar_ratioP [hlow' _] h1.
rewrite -ler_pdivrMl //; apply: hglb=> s hs.
have [s' hs' hle] := h1 _ hs; rewrite ler_pdivrMl //; exact: le_trans (hlow' _ hs') hle.
Qed.

(** Source for [is_haar_ratio_zero]: (0:v) = 0, the case c = 0 of
    "(cu:v) = c(u:v)", Federer 2.7.4, p. 123, where the empty family
    belongs to C(0,v). Supporting lemma. *)
Lemma is_haar_ratio_zero v : is_haar_ratio A (fun _ => 0) v 0.
Proof.
apply/is_haar_ratioP; split; first by move=> s; exact: haar_family_total_nonneg.
move=> b hb; have := hb [::]; rewrite /haar_family_total big_nil; apply.
by split=> // x; rewrite big_nil.
Qed.

(** Source for [is_haar_ratio_monotone]: "u_1 <= u_2 implies
    (u_1:v) <= (u_2:v)", Federer 2.7.4, p. 123: C(u_2,v) is contained in
    C(u_1,v). Direct formalisation for given infima. *)
Lemma is_haar_ratio_monotone u1 u2 v r1 r2 : function_le u1 u2 ->
  is_haar_ratio A u1 v r1 -> is_haar_ratio A u2 v r2 -> r1 <= r2.
Proof.
move=> h12 h1 h2; rewrite -[r2]mul1r; apply: (haar_ratio_le_transfer ltr01 h2 h1).
move=> s [hs hle]; exists s; last by rewrite mul1r.
by split=> // x; exact: le_trans (h12 x) (hle x).
Qed.

(** Source for [is_haar_ratio_scale]: "(cu:v) = c(u:v) for
    0 < c < oo", Federer 2.7.4, p. 123: multiplication of the
    coefficients by c maps C(u,v) onto C(cu,v). Direct formalisation for
    a given infimum. *)
Lemma is_haar_ratio_scale u v r c : 0 < c -> is_haar_ratio A u v r ->
  is_haar_ratio A (fun x => c * u x) v (c * r).
Proof.
move=> hc hr; apply: (is_haar_ratio_transfer hc hr).
- move=> s [hs hle]; exists [seq (p.1, c * p.2) | p <- s].
    split; first by move=> q /mapP [p hp ->]; apply: mulr_ge0; [exact: ltW|exact: hs].
    move=> x; rewrite big_map /=; under eq_bigr do rewrite -mulrA; rewrite -mulr_sumr.
    by rewrite ler_pM2l //; exact: hle.
  by rewrite /haar_family_total big_map -mulr_sumr.
- move=> s [hs hle]; exists [seq (p.1, c^-1 * p.2) | p <- s].
    split; first by move=> q /mapP [p hp ->]; apply: mulr_ge0; [rewrite invr_ge0; exact: ltW|exact: hs].
    move=> x; rewrite big_map /=; under eq_bigr do rewrite -mulrA; rewrite -mulr_sumr.
    by rewrite ler_pdivlMl //; exact: hle.
  by rewrite /haar_family_total big_map -mulr_sumr mulrA mulfV ?mul1r // gt_eqF.
Qed.

(** Source for [is_haar_ratio_add]: "(u_1+u_2:v) <= (u_1:v)+(u_2:v)",
    Federer 2.7.4, p. 123: the union of a family for u_1 and a family for
    u_2 is a family for u_1+u_2. Direct formalisation for given
    infima. *)
Lemma is_haar_ratio_add u1 u2 v r1 r2 r : is_haar_ratio A u1 v r1 -> is_haar_ratio A u2 v r2 ->
  is_haar_ratio A (fun x => u1 x + u2 x) v r -> r <= r1 + r2.
Proof.
move=> h1 h2 h; apply/ler_addgt0Pr=> eps he.
have he2 : 0 < eps / 2 by rewrite divr_gt0.
have [s1 hs1 ht1] := haar_ratio_approx h1 he2.
have [s2 hs2 ht2] := haar_ratio_approx h2 he2.
have hcov : haar_family_cover (fun x => u1 x + u2 x) v (s1 ++ s2).
  case: hs1 hs2=> [hc1 hl1] [hc2 hl2]; split.
    by move=> p; rewrite mem_cat=> /orP [/hc1|/hc2].
  by move=> x; rewrite big_cat; apply: lerD; [exact: hl1|exact: hl2].
have := haar_ratio_lower h hcov; rewrite /haar_family_total big_cat /=.
rewrite /haar_family_total in ht1 ht2; move=> hle; lra.
Qed.

(** Source for [le_mul_of_forall_pos]: the passage from
    (u:w) <= (sum_G xi).(sum_G eta) to (u:w) <= (u:v).(v:w) in Federer
    2.7.4, p. 124, by approximation of the infima. Supporting lemma on
    real numbers. *)
Lemma le_mul_of_forall_pos (a b c : R) : 0 <= b -> 0 <= c ->
  (forall eps, 0 < eps -> a <= (b + eps) * (c + eps)) -> a <= b * c.
Proof.
move=> hb hc h; apply/ler_addgt0Pr=> d hd.
have hbc : 0 < b + c + 1 by lra.
pose eps := Order.min 1 (d / (b + c + 1)).
have he : 0 < eps by rewrite lt_min ltr01 divr_gt0.
have he1 : eps <= 1 by rewrite ge_min lexx.
have he2 : eps * (b + c + 1) <= d.
  by rewrite -ler_pdivlMr // ge_min lexx orbT.
have := h eps he; move=> hle; nra.
Qed.

(** Source for [is_haar_ratio_mul]: "(u:w) <= (u:v).(v:w) because
    xi in C(u,v) and eta in C(v,w) implies u <= sum_{g in G} xi(g)
    sum_{h in G} eta(h)(w o A_h o A_g) = sum_{k in G} zeta(k)(w o A_k)",
    Federer 2.7.4, p. 124. Direct formalisation for given infima; the
    composite family consists of the pairs (hg, xi(g) eta(h)), whose sum
    is sum_G xi . sum_G eta. *)
Lemma is_haar_ratio_mul (mul : G -> G -> G) u v w r1 r2 r :
  (forall g h x, A (mul g h) x = A g (A h x)) ->
  is_haar_ratio A u v r1 -> is_haar_ratio A v w r2 -> is_haar_ratio A u w r -> r <= r1 * r2.
Proof.
move=> hcomp h1 h2 h.
apply: le_mul_of_forall_pos; [exact: haar_ratio_nonneg h1|exact: haar_ratio_nonneg h2|].
move=> eps he.
have [s hs hts] := haar_ratio_approx h1 he.
have [t ht htt] := haar_ratio_approx h2 he.
pose st := [seq (mul q.1 p.1, p.2 * q.2) | p <- s, q <- t].
have hcov : haar_family_cover u w st.
  case: hs ht=> [hcs hls] [hct hlt]; split.
    move=> z /allpairsP [[p q] [hp hq ->]] /=; apply: mulr_ge0; [exact: hcs|exact: hct].
  move=> x; rewrite big_allpairs_dep /=; apply: le_trans (hls x) _.
  rewrite big_seq [X in _ <= X]big_seq; apply: ler_sum=> p hp.
  have hsum : \sum_(q <- t) p.2 * q.2 * w (A (mul q.1 p.1) x) =
      p.2 * \sum_(q <- t) q.2 * w (A q.1 (A p.1 x)).
    by rewrite mulr_sumr; apply: eq_bigr=> q _; rewrite hcomp mulrA.
  by rewrite hsum; apply: ler_wpM2l; [exact: hcs|exact: hlt].
have htot : haar_family_total st = haar_family_total s * haar_family_total t.
  rewrite /haar_family_total big_allpairs_dep /= mulr_suml; apply: eq_bigr=> p _.
  by rewrite mulr_sumr.
have := haar_ratio_lower h hcov; rewrite htot=> hle.
have h0s := haar_family_total_nonneg hs; have h0t := haar_family_total_nonneg ht.
apply: le_trans hle _; apply: ler_pM=> //; exact: ltW.
Qed.

End HaarFamilies.

Section HaarRatioLaws.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Local Notation K := (@compactly_supported_continuous_functions R X).
Local Notation Kp := (positive_function_lattice K).
Implicit Types (u v w : X -> R) (r c : R) (s : seq (G * R)) (rho : (X -> R) -> (X -> R) -> R).

(** Source for [compactly_supported_upper_bound]: a member of K(X) is
    bounded above, as presupposed by "sup im u" in Federer 2.7.4,
    p. 123: its maximum on the compact support is attained (2.5.13,
    p. 106). Supporting lemma. *)
Lemma compactly_supported_upper_bound u : K u -> exists M, 0 <= M /\ forall x, u x <= M.
Proof.
case=> hc hK; case: (pselect (real_function_support u !=set0))=> hne.
  have hc' : continuous (u : X -> R^o) by move=> x; exact: hc x.
  have [x0 [hx0 hmax]] := @continuous_compact_maximum R X _ u hne hK hc'.
  exists (Order.max (u x0) 0); split; first by rewrite le_max lexx orbT.
  move=> x; case: (pselect (real_function_support u x))=> hx.
    by apply: le_trans (hmax x hx) _; rewrite le_max lexx.
  by rewrite (real_function_zero_off_support hx) le_max lexx orbT.
exists 0; split=> // x; rewrite (real_function_zero_off_support (x:=x)) //.
by move=> hx; apply: hne; exists x.
Qed.

(** Source for [sum_ge_term]: a term of a finite sum of nonnegative
    numbers is at most the sum, as used for "C(u,v) <> empty" in
    Federer 2.7.4, p. 123. Supporting lemma. *)
Lemma sum_ge_term (I : eqType) (r : seq I) (F : I -> R) i : uniq r -> i \in r ->
  (forall j, j \in r -> 0 <= F j) -> F i <= \sum_(j <- r) F j.
Proof.
move=> hu hi h0; rewrite (bigD1_seq i) //= lerDl big_seq_cond.
by apply: sumr_ge0=> j /andP [hj _]; exact: h0.
Qed.

(** Source for [haar_family_cover_exists]: "Obviously C(u,v) <> empty",
    Federer 2.7.4, p. 123, for finite families. If v(b) > 0, choose for
    each x in X some g_x with A(g_x,x) = b (transitivity, 2.7.1,
    p. 121); the open sets {x: v(A(g_x,x)) > v(b)/2} cover the compact
    set spt u, and if x_1, ..., x_n give a finite subcover and M bounds
    u, the family of the pairs (g_{x_i}, 2M/v(b)) belongs to C(u,v). *)
Lemma haar_family_cover_exists u v : Kp u -> Kp v -> (exists b, v b <> 0) ->
  exists s, haar_family_cover A u v s.
Proof.
move=> [hu hu0] [hv hv0] [b hb].
have hvb : 0 < v b by rewrite lt_neqAle eq_sym; apply/andP; split; [apply/eqP|exact: hv0].
pose c := v b / 2.
have hc : 0 < c by rewrite divr_gt0.
have hcb : c < v b by rewrite /c ltr_pdivrMr // ltr_pMr // ltr1n.
have /choice [gx hgx] : forall x, exists g, A g x = b := fun x => homogeneous_transitive hA x b.
pose O x := A (gx x) @^-1` (v @^-1` [set t | c < t]).
have hO x : open (O x).
  apply: open_comp; last apply: open_comp; last exact: open_gt.
  - by move=> y _; exact: homogeneous_translation_continuous hA (gx x) y.
  - by move=> y _; exact: (hv.1 y).
have hxO x : O x x by rewrite /O /= hgx.
have [M [hM0 hM]] := compactly_supported_upper_bound hu.
have [D hDsub hDcov] := @compact_open_finite_cover X X (real_function_support u) O _ hu.2
  (fun x _ => hO x) (fun x hx => ex_intro2 _ (fun j => O j x) x hx (hxO x)).
exists [seq (gx y, M / c) | y <- D]; split.
  by move=> p /mapP [y _ ->]; rewrite divr_ge0 // ltW.
move=> x; rewrite big_map.
have hnn y : 0 <= M / c * v (A (gx y) x).
  by apply: mulr_ge0; [rewrite divr_ge0 // ltW|exact: hv0].
case: (pselect (real_function_support u x))=> hx.
  have [y hy hOy] := hDcov x hx.
  apply: le_trans (hM x) _; apply: le_trans (sum_ge_term (fset_uniq D) hy (fun j _ => hnn j)).
  have hle : M / c * c <= M / c * v (A (gx y) x).
    by apply: ler_wpM2l; [rewrite divr_ge0 // ltW|exact: ltW].
  by rewrite divfK ?gt_eqF // in hle.
rewrite (real_function_zero_off_support hx) big_seq; apply: sumr_ge0=> y _; exact: hnn.
Qed.

(** Source for [haar_cover_nonempty]: "Obviously C(u,v) <> empty",
    Federer 2.7.4, p. 123. Direct formalisation for u in K(X)+ and
    0 <> v in K(X)+. *)
Theorem haar_cover_nonempty u v : Kp u -> Kp v -> (exists b, v b <> 0) ->
  haar_cover A u v !=set0.
Proof.
move=> hu hv hb; have [s hs] := haar_family_cover_exists hu hv hb.
by exists (family_function s); exact: (haar_family_cover_function hs).1.
Qed.

(** Source for [is_haar_ratio_exists]: "we define the so-called Haar
    ratio (u:v) = inf{sum_G xi: xi in C(u,v)}", Federer 2.7.4, p. 123:
    the infimum exists, since C(u,v) is nonempty and the sums are
    nonnegative. Existence for given u in K(X)+ and 0 <> v in K(X)+. *)
Lemma is_haar_ratio_exists u v : Kp u -> Kp v -> (exists b, v b <> 0) ->
  exists r, is_haar_ratio A u v r.
Proof.
move=> hu hv hb.
pose S := [set group_sum xi | xi in haar_cover A u v].
have hS : S !=set0.
  by have [xi hxi] := haar_cover_nonempty hu hv hb; exists (group_sum xi), xi.
have hlb : lbound S 0.
  move=> _ [xi hxi <-]; have [s [hs <-]] := haar_cover_family hxi.
  exact: haar_family_total_nonneg hs.
exists (inf S); split.
- by move=> xi hxi; apply: ge_inf; [exists 0|exists xi].
- by move=> b hb'; apply: lb_le_inf=> // _ [xi hxi <-]; exact: hb'.
Qed.

(** Source for [haar_ratio_function_exists]: the Haar ratio (u:v) of
    Federer 2.7.4, p. 123, is defined whenever u in K(X)+ and
    0 <> v in K(X)+. Existence of a Haar ratio function, by choice. *)
Theorem haar_ratio_function_exists :
  exists rho : (X -> R) -> (X -> R) -> R, is_haar_ratio_function A rho.
Proof.
exists (fun u v => if pselect (exists r, is_haar_ratio A u v r) is left h then projT1 (cid h) else 0).
move=> u v hu hv hb; case: pselect=> [h|hn]; first exact: projT2 (cid h).
by exfalso; apply: hn; exact: is_haar_ratio_exists.
Qed.

(** Source for [is_haar_ratio_sup_bound]: "(u:v) >= sup im u/sup im v",
    Federer 2.7.4, p. 123: if u <= sum_i c_i (v o A_{g_i}), then
    sup im u <= (sum_i c_i) sup im v. Direct formalisation for a given
    infimum. *)
Lemma is_haar_ratio_sup_bound u v r : Kp u -> Kp v -> (exists b, v b <> 0) ->
  is_haar_ratio A u v r -> sup (range u) / sup (range v) <= r.
Proof.
move=> [hu hu0] [hv hv0] [b hb] /is_haar_ratioP [_ hglb].
have hvb : 0 < v b by rewrite lt_neqAle eq_sym; apply/andP; split; [apply/eqP|exact: hv0].
have [Mv [_ hMv]] := compactly_supported_upper_bound hv.
have hub : has_ubound (range v) by exists Mv=> _ [y _ <-]; exact: hMv.
have hvsup y : v y <= sup (range v) by apply: ub_le_sup hub _ _; exists y.
have hsv : 0 < sup (range v) := lt_le_trans hvb (hvsup b).
apply: hglb=> s [hs hle]; rewrite ler_pdivrMr //.
apply: ge_sup; first by exists (u b), b.
move=> _ [x _ <-]; apply: le_trans (hle x) _.
rewrite /haar_family_total mulr_suml big_seq [X in _ <= X]big_seq; apply: ler_sum=> p hp.
by apply: ler_wpM2l; [exact: hs|exact: hvsup].
Qed.

(** Source for [is_haar_ratio_translate]: "(u o A_h:v) = (u:v) for
    h in G", Federer 2.7.4, p. 123: a family (g_i, c_i) for u yields the
    family (g_i h, c_i) for u o A_h, and conversely with h^{-1}, since
    A_{gh} = A_g o A_h. Direct formalisation for a given infimum. *)
Lemma is_haar_ratio_translate u v r h : is_haar_ratio A u v r -> is_haar_ratio A (u \o A h) v r.
Proof.
move=> hr; rewrite -[r]mul1r; apply: (is_haar_ratio_transfer ltr01 hr).
- move=> s [hs hle]; exists [seq (mul p.1 h, p.2) | p <- s]; last first.
    by rewrite mul1r /haar_family_total big_map.
  split; first by move=> q /mapP [p hp ->]; exact: (hs p hp).
  move=> x; rewrite big_map /=; apply: le_trans (hle (A h x)) _.
  by apply: ler_sum=> p _; rewrite (homogeneous_action_compatible hA).
- move=> s [hs hle]; exists [seq (mul p.1 (inv h), p.2) | p <- s]; last first.
    by rewrite mul1r /haar_family_total big_map.
  split; first by move=> q /mapP [p hp ->]; exact: (hs p hp).
  move=> x; rewrite big_map /=.
  have := hle (A (inv h) x); rewrite /= (homogeneous_translation_inverse_right hG hA).
  move=> hle'; apply: le_trans hle' _.
  by apply: ler_sum=> p _; rewrite (homogeneous_action_compatible hA).
Qed.

(** Source for [haar_ratio_translate]: "(u o A_h:v) = (u:v) for
    h in G", Federer 2.7.4, p. 123. Direct formalisation. *)
Theorem haar_ratio_translate rho u v h : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> (exists b, v b <> 0) -> rho (u \o A h) v = rho u v.
Proof.
move=> hrho hu hv hb.
have hut : Kp (u \o A h).
  split; first exact: (compactly_supported_translate hG hA h hu.1).
  by move=> x; exact: hu.2.
apply: (haar_ratio_unique (hrho _ _ hut hv hb)).
exact: is_haar_ratio_translate (hrho _ _ hu hv hb).
Qed.

(** Source for [haar_ratio_sup_bound]: "(u:v) >= sup im u/sup im v",
    Federer 2.7.4, p. 123. Direct formalisation. *)
Theorem haar_ratio_sup_bound rho u v : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> (exists b, v b <> 0) -> sup (range u) / sup (range v) <= rho u v.
Proof. by move=> hrho hu hv hb; exact: is_haar_ratio_sup_bound hu hv hb (hrho _ _ hu hv hb). Qed.

(** Source for [haar_ratio_scale]: "(cu:v) = c(u:v) for 0 < c < oo",
    Federer 2.7.4, p. 123. Direct formalisation. *)
Theorem haar_ratio_scale rho u v c : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> (exists b, v b <> 0) -> 0 < c -> rho (fun x => c * u x) v = c * rho u v.
Proof.
move=> hrho hu hv hb hc.
have hcu : Kp (fun x => c * u x).
  split; first exact: (@function_lattice_scale R X K
    (compactly_supported_continuous_functions_lattice R X) c u (ltW hc) hu.1).
  by move=> x; apply: mulr_ge0; [exact: ltW|exact: hu.2].
apply: (haar_ratio_unique (hrho _ _ hcu hv hb)).
exact: is_haar_ratio_scale hc (hrho _ _ hu hv hb).
Qed.

(** Source for [haar_ratio_add]: "(u_1+u_2:v) <= (u_1:v)+(u_2:v)",
    Federer 2.7.4, p. 123. Direct formalisation. *)
Theorem haar_ratio_add rho u1 u2 v : is_haar_ratio_function A rho ->
  Kp u1 -> Kp u2 -> Kp v -> (exists b, v b <> 0) ->
  rho (fun x => u1 x + u2 x) v <= rho u1 v + rho u2 v.
Proof.
move=> hrho hu1 hu2 hv hb.
have hu : Kp (fun x => u1 x + u2 x).
  split; first exact: (@function_lattice_add R X K
    (compactly_supported_continuous_functions_lattice R X) u1 u2 hu1.1 hu2.1).
  by move=> x; apply: addr_ge0; [exact: hu1.2|exact: hu2.2].
exact: is_haar_ratio_add (hrho _ _ hu1 hv hb) (hrho _ _ hu2 hv hb) (hrho _ _ hu hv hb).
Qed.

(** Source for [haar_ratio_monotone]: "u_1 <= u_2 implies
    (u_1:v) <= (u_2:v)", Federer 2.7.4, p. 123. Direct formalisation. *)
Theorem haar_ratio_monotone rho u1 u2 v : is_haar_ratio_function A rho ->
  Kp u1 -> Kp u2 -> Kp v -> (exists b, v b <> 0) -> function_le u1 u2 -> rho u1 v <= rho u2 v.
Proof.
move=> hrho hu1 hu2 hv hb h12.
exact: is_haar_ratio_monotone h12 (hrho _ _ hu1 hv hb) (hrho _ _ hu2 hv hb).
Qed.

(** Source for [haar_ratio_zero]: (0:v) = 0, the case c = 0 of
    "(cu:v) = c(u:v)", Federer 2.7.4, p. 123. Supporting theorem. *)
Theorem haar_ratio_zero rho v : is_haar_ratio_function A rho ->
  Kp v -> (exists b, v b <> 0) -> rho (fun _ => 0) v = 0.
Proof.
move=> hrho hv hb.
have h0 : Kp (fun _ : X => 0) by split; [exact: compactly_supported_zero_function|move=> x].
exact: haar_ratio_unique (hrho _ _ h0 hv hb) (is_haar_ratio_zero A v).
Qed.

(** Source for [haar_ratio_nonnegative]: (u:v) >= 0, Federer 2.7.4,
    p. 123, from "xi: G -> {t: 0 <= t < oo}". Supporting theorem. *)
Theorem haar_ratio_nonnegative rho u v : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> (exists b, v b <> 0) -> 0 <= rho u v.
Proof. by move=> hrho hu hv hb; exact: haar_ratio_nonneg (hrho _ _ hu hv hb). Qed.

(** Source for [haar_ratio_mul]: "if u, v, w in K(X)+ are nonzero,
    then (u:w) <= (u:v).(v:w)", Federer 2.7.4, p. 124. Direct
    formalisation; only v and w need to be nonzero, since (u:v) and
    (u:w) are defined for every u in K(X)+. *)
Theorem haar_ratio_mul rho u v w : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> Kp w -> (exists b, v b <> 0) -> (exists b, w b <> 0) ->
  rho u w <= rho u v * rho v w.
Proof.
move=> hrho hu hv hw hbv hbw.
exact: is_haar_ratio_mul (homogeneous_action_compatible hA)
  (hrho _ _ hu hv hbv) (hrho _ _ hv hw hbw) (hrho _ _ hu hw hbw).
Qed.

(** Source for [haar_ratio_positive]: for nonzero u and v in K(X)+,
    (u:v) >= sup im u/sup im v > 0, Federer 2.7.4, p. 123, as used in
    "1/(w:u)" on p. 124. Supporting theorem. *)
Theorem haar_ratio_positive rho u v : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> (exists b, u b <> 0) -> (exists b, v b <> 0) -> 0 < rho u v.
Proof.
move=> hrho hu hv [a ha] hbv.
have hua : 0 < u a by rewrite lt_neqAle eq_sym; apply/andP; split; [apply/eqP|exact: hu.2].
have hsup f : Kp f -> forall y, f y <= sup (range f).
  move=> hf y; have [M [_ hM]] := compactly_supported_upper_bound hf.1.
  by apply: ub_le_sup; [exists M=> _ [z _ <-]; exact: hM|exists y].
have hsu : 0 < sup (range u) := lt_le_trans hua (hsup u hu a).
have [b hb] := hbv.
have hvb : 0 < v b by rewrite lt_neqAle eq_sym; apply/andP; split; [apply/eqP|exact: hv.2].
have hsv : 0 < sup (range v) := lt_le_trans hvb (hsup v hv b).
apply: lt_le_trans (haar_ratio_sup_bound hrho hu hv hbv); exact: divr_gt0.
Qed.

(** Source for [haar_ratio_quotient_bounds]: "Consequently
    1/(w:u) <= (u:v)/(w:v) <= (u:w)", Federer 2.7.4, p. 124, for
    nonzero u, v, w in K(X)+. Direct formalisation: (w:v) <= (w:u)(u:v)
    and (u:v) <= (u:w)(w:v). *)
Theorem haar_ratio_quotient_bounds rho u v w : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> Kp w -> (exists b, u b <> 0) -> (exists b, v b <> 0) -> (exists b, w b <> 0) ->
  1 / rho w u <= rho u v / rho w v <= rho u w.
Proof.
move=> hrho hu hv hw hbu hbv hbw.
have hwu := haar_ratio_positive hrho hw hu hbw hbu.
have hwv := haar_ratio_positive hrho hw hv hbw hbv.
apply/andP; split.
  rewrite ler_pdivrMr // mulrAC ler_pdivlMr // mul1r [X in _ <= X]mulrC.
  exact: haar_ratio_mul hrho hw hu hv hbu hbv.
by rewrite ler_pdivrMr //; exact: haar_ratio_mul hrho hu hw hv hbw hbv.
Qed.

(** Source for [haar_ratio_quotient_upper]: the right inequality
    "(u:v)/(w:v) <= (u:w)" of Federer 2.7.4, p. 124, which holds for
    every u in K(X)+ when v and w are nonzero. Supporting theorem,
    used for p_v in P. *)
Theorem haar_ratio_quotient_upper rho u v w : is_haar_ratio_function A rho ->
  Kp u -> Kp v -> Kp w -> (exists b, v b <> 0) -> (exists b, w b <> 0) ->
  rho u v / rho w v <= rho u w.
Proof.
move=> hrho hu hv hw hbv hbw.
have hwv := haar_ratio_positive hrho hw hv hbw hbv.
by rewrite ler_pdivrMr //; exact: haar_ratio_mul hrho hu hw hv hbw hbv.
Qed.

End HaarRatioLaws.
