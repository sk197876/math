(** Federer (1969), 2.5.17, pp. 110-111: for g : R -> R with V_a^b g < oo
    whenever -oo < a < b < oo and f continuous, the Riemann-Stieltjes sums
    converge, as delta tends to 0+, to a real number, the integral of f with
    respect to g from a to b; the operation is linear with respect to f,
    satisfies |int_a^b f dg| <= sup{|f(x)| : a <= x <= b} V_a^b g, and
    int_a^b f dg + int_b^c f dg = int_a^c f dg whenever a <= b <= c. The
    integral is the limit of the sums over the uniform sequences with left
    tags; the convergence of every sequence of sums with mesh tending to
    zero is the printed characterisation. Federer states the integral for f
    in K(R); the construction only uses the continuity of f on [a, b]. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBoundsUP ExtendedRealBounds
  ArchimedeanReciprocal CurveVariationUP CurveArcLength SegmentUniformContinuity StieltjesSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section StieltjesIntegral.
Variable R : realType.
Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
(** Source for [total_variation]: V_a^b g as a real number under the
    hypothesis of Federer 2.5.17, p. 110, that V_a^b g < oo. *)
Definition total_variation (a b : R) : R := fine (curve_variation (g : R -> real_line_metric R) a b).

(** Source for [absolute_chain_chain_sum]: the absolute increment sum of
    g is the chain sum of g as a curve in the real line, Federer 2.5.17,
    p. 111, and 2.5.16, p. 109. *)
Lemma absolute_chain_chain_sum (M : seq R) :
  absolute_chain g M = chain_sum (g : R -> real_line_metric R) M.
Proof.
elim: M=> [//|t M ih]; case: M ih=> [//|t' M] ih.
by rewrite absolute_chain_cons2 chain_sum_cons ih real_line_metric_distanceE distrC.
Qed.

(** Source for [variation_nonnegative_fine]: supporting nonnegativity
    of V_a^b g as a real number, Federer 2.5.16, p. 109. *)
Lemma variation_nonnegative_fine (a b : R) : a <= b -> 0 <= total_variation a b.
Proof. by move=> hab; rewrite /total_variation; exact (fine_ge0 (curve_variation_nonnegative _ hab)). Qed.

(** Source for [absolute_chain_le_variation]: the absolute increment sum
    over a nondecreasing list from a to b is at most V_a^b g, Federer
    2.5.17, p. 111. *)
Lemma absolute_chain_le_variation (a b : R) (M : seq R) :
  a <= b -> sorted <=%O M -> head 0 M = a -> last 0 M = b -> M <> [::] ->
  absolute_chain g M <= total_variation a b.
Proof.
move=> hab hM hh hl hne.
have hfin := curve_variation_fin_num hg hab.
case: (leqP (size M) 1)=> hsize.
- have hconst : forall x, x \in M -> x = a.
    case: M hsize hh hl hne hM=> [//|m [|m' M]] //= _ -> hl _ _ x; rewrite inE=> /eqP ->.
    by [].
  by rewrite (absolute_chain_constant g hconst); exact: variation_nonnegative_fine.
- have hpart : is_variation_partition a b M.
    split=> //; split=> //; split.
    + by rewrite -hh; case: M hne {hM hh hl hsize}.
    + by rewrite -hl; case: M hne {hM hh hl hsize}.
  have hle : ((chain_sum (g : R -> real_line_metric R) M)%:E
      <= curve_variation (g : R -> real_line_metric R) a b)%E :=
    extended_real_sup_upper (ex_intro _ M (conj hpart erefl)).
  by rewrite absolute_chain_chain_sum /total_variation -lee_fin (fineK hfin).
Qed.

(** Source for [uniform_tagged]: the sequence a = t_1 = u_1 <= t_2 = u_2
    <= ... with t_{i+1} - t_i = h and left tags, Federer 2.5.17,
    p. 111. *)
Fixpoint uniform_tagged (a h : R) (n : nat) : seq R :=
  if n is k.+1 then a :: a :: uniform_tagged (a + h) h k else [:: a].

(** Source for [uniform_tagged_ge]: supporting lower bound of the
    uniform sequence by its start, Federer 2.5.17, p. 111. *)
Lemma uniform_tagged_ge (a h : R) (n : nat) :
  0 <= h -> all (fun x => a <= x) (uniform_tagged a h n).
Proof.
elim: n a=> [|k ih] a hh /=; first by rewrite lexx.
rewrite !lexx /=; apply: sub_all (ih (a + h) hh)=> x hx.
by apply: le_trans hx; rewrite lerDl.
Qed.

(** Source for [uniform_tagged_path]: supporting path property of the
    uniform sequence from a point below its start, Federer 2.5.17,
    p. 111. *)
Lemma uniform_tagged_path (x a h : R) (n : nat) :
  0 <= h -> x <= a -> path <=%O x (uniform_tagged a h n).
Proof.
elim: n x a=> [|k ih] x a hh hxa /=; first by rewrite hxa.
by rewrite hxa lexx /=; apply: ih=> //; rewrite lerDl.
Qed.

(** Source for [uniform_tagged_sorted]: the uniform sequence is
    nondecreasing, Federer 2.5.17, p. 111. *)
Lemma uniform_tagged_sorted (a h : R) (n : nat) : 0 <= h -> sorted <=%O (uniform_tagged a h n).
Proof.
case: n=> [//|k] hh; rewrite /= lexx /=.
by apply: uniform_tagged_path=> //; rewrite lerDl.
Qed.

(** Source for [uniform_tagged_size]: the uniform sequence with n cells
    has 2n+1 terms, Federer 2.5.17, p. 111. *)
Lemma uniform_tagged_size (a h : R) (n : nat) : size (uniform_tagged a h n) = (2 * n).+1.
Proof. by elim: n a=> [//|k ih] a /=; rewrite ih mulnS. Qed.

(** Source for [uniform_tagged_head]: the first term is a, Federer
    2.5.17, p. 111. *)
Lemma uniform_tagged_head (a h x : R) (n : nat) : head x (uniform_tagged a h n) = a.
Proof. by case: n. Qed.

(** Source for [uniform_tagged_last]: the last term is a + n h, Federer
    2.5.17, p. 111. *)
Lemma uniform_tagged_last (a h x : R) (n : nat) : last x (uniform_tagged a h n) = a + n%:R * h.
Proof.
elim: n a x=> [|k ih] a x /=; first by rewrite mul0r addr0.
by rewrite ih -addn1 natrD mulrDl mul1r; ring.
Qed.

(** Source for [uniform_tagged_mesh]: the cells of the uniform sequence
    have length h, Federer 2.5.17, p. 111. *)
Lemma uniform_tagged_mesh (a h d : R) (n : nat) : h < d -> tagged_mesh_lt d (uniform_tagged a h n).
Proof.
elim: n a=> [//|k ih] a hd; rewrite /=.
case: k ih=> [|k'] ih /=.
- by rewrite (_ : a + h - a = h) ?hd //; ring.
- apply/andP; split; first by rewrite (_ : a + h - a = h) //; ring.
  exact: ih.
Qed.

(** Source for [uniform_partition]: the uniform sequence of [a, b] with
    n+1 cells, Federer 2.5.17, p. 111. *)
Definition uniform_partition (a b : R) (n : nat) : seq R :=
  uniform_tagged a ((b - a) / n.+1%:R) n.+1.

(** Source for [uniform_partition_is]: the uniform sequence is a
    sequence from a to b, Federer 2.5.17, p. 111. *)
Lemma uniform_partition_is (a b : R) (n : nat) : a <= b -> is_tagged_partition a b (uniform_partition a b n).
Proof.
move=> hab; have hh : 0 <= (b - a) / n.+1%:R by rewrite divr_ge0 ?subr_ge0 ?ler0n.
split; first exact: uniform_tagged_sorted.
split; first by rewrite uniform_tagged_size mul2n /= odd_double.
split; first exact: uniform_tagged_head.
rewrite uniform_tagged_last mulrC mulfVK ?pnatr_eq0 //.
by rewrite addrC subrK.
Qed.

(** Source for [uniform_partition_mesh]: the mesh of the uniform
    sequence is (b - a)/(n+1), Federer 2.5.17, p. 111. *)
Lemma uniform_partition_mesh (a b d : R) (n : nat) :
  (b - a) / n.+1%:R < d -> tagged_mesh_lt d (uniform_partition a b n).
Proof. exact: uniform_tagged_mesh. Qed.

(** Source for [uniform_mesh_small]: for every positive delta some
    uniform sequence has mesh below delta, by the Archimedean property,
    Federer 2.5.17, p. 111. *)
Lemma uniform_mesh_small (a b d : R) :
  a <= b -> 0 < d -> exists N : nat, forall n, (N <= n)%N -> (b - a) / n.+1%:R < d.
Proof.
move=> hab hd; case: (ltgtP 0 (b - a))=> [hba|hba|hba]; last first.
- by exists 0%N=> n _; rewrite -hba mul0r.
- by move: hba; rewrite ltNge subr_ge0 hab.
- have [N hN] := real_reciprocal_below (divr_gt0 hd hba).
  exists N=> n hn.
  have hle : n.+1%:R^-1 <= N.+1%:R^-1 :> R.
    by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
  rewrite -(ltr_pM2l hba) in hN.
  apply: le_lt_trans (ler_wpM2l (ltW hba) hle) _.
  apply: lt_le_trans hN _.
  have hne : b - a != 0 := lt0r_neq0 hba.
  by rewrite mulrC (mulfVK hne).
Qed.

(** Source for [fine_partitions_close]: two Riemann-Stieltjes sums with
    mesh below a suitable delta differ by at most e, the diameter
    estimate 2 sup{|f(u) - f(v)| : |u - v| <= delta} V_a^b g of Federer
    2.5.17, p. 111, combined with uniform continuity. *)
Lemma fine_partitions_close (f : R -> R) (a b e : R) :
  continuous f -> a <= b -> 0 < e ->
  exists d, 0 < d /\ forall w w', is_tagged_partition a b w -> is_tagged_partition a b w' ->
    tagged_mesh_lt d w -> tagged_mesh_lt d w' ->
    `|stieltjes_sum f g w - stieltjes_sum f g w'| <= e.
Proof.
move=> hf hab he.
have hV0 : 0 <= total_variation a b := variation_nonnegative_fine hab.
have hV1 : 0 < total_variation a b + 1 by lra.
pose om := e / (2 * (total_variation a b + 1)).
have hom : 0 < om by rewrite /om divr_gt0 // mulr_gt0 ?ltr0n.
have [d [hd hdprop]] := segment_uniform_continuity a b hf hom.
exists (d / 2); split; first by rewrite divr_gt0 ?ltr0n.
move=> w w' hw hw' hm hm'.
have homb : forall x y, a <= x <= b -> a <= y <= b -> `|x - y| <= d / 2 -> `|f x - f y| <= om.
  move=> x y hx hy hxy; apply: ltW; apply: hdprop=> //.
  by apply: le_lt_trans hxy _; lra.
have [M [hM [hh [hl hest]]]] := tagged_pair_estimate g hw hw' hm hm' homb.
apply: le_trans hest _.
case: (pselect (M = [::]))=> [hnil|hne].
  by rewrite hnil /= mulr0; exact: ltW.
have hAC := absolute_chain_le_variation hab hM hh hl hne.
have hAC0 := absolute_chain_nonnegative g M.
have -> : e = 2 * om * (total_variation a b + 1).
  by rewrite /om; field; exact (lt0r_neq0 hV1).
apply: ler_wpM2l; first by rewrite mulr_ge0 ?ler0n // ltW.
by apply: le_trans hAC _; rewrite lerDl.
Qed.

(** Source for [tagged_mesh_lt_le]: supporting monotonicity of the
    mesh condition in delta, Federer 2.5.17, p. 111. *)
Lemma tagged_mesh_lt_le (d d' : R) (w : seq R) :
  d <= d' -> tagged_mesh_lt d w -> tagged_mesh_lt d' w.
Proof.
move=> hdd'; have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize //.
rewrite !tagged_mesh_lt_cons=> /andP[h1 h2]; rewrite (lt_le_trans h1 hdd') andTb.
by apply: ih=> //; move: hsize; rewrite /= ltnS; exact: ltnW.
Qed.

(** Source for [uniform_sums]: the Riemann-Stieltjes sums over the
    uniform sequences, Federer 2.5.17, p. 111. *)
Definition uniform_sums (f : R -> R) (a b : R) (n : nat) : R :=
  stieltjes_sum f g (uniform_partition a b n).

(** Source for [stieltjes_integral]: the real number int_a^b f dg of
    Federer 2.5.17, p. 111, as the limit of the uniform sums. *)
Definition stieltjes_integral (f : R -> R) (a b : R) : R := limn (uniform_sums f a b).

(** Source for [uniform_sums_cauchy]: the uniform sums form a Cauchy
    sequence, Federer 2.5.17, p. 111. *)
Lemma uniform_sums_cauchy (f : R -> R) (a b : R) :
  continuous f -> a <= b -> cauchy (uniform_sums f a b @ \oo).
Proof.
move=> hf hab; apply/cauchyP=> e he.
have he2 : 0 < e / 2 by lra.
have [d [hd hclose]] := fine_partitions_close hf hab he2.
have [N hN] := uniform_mesh_small hab hd.
exists (uniform_sums f a b N).
suff : \forall n \near \oo, ball (uniform_sums f a b N) e (uniform_sums f a b n) by [].
near=> n; rewrite /ball /=.
have hn : (N <= n)%N by near: n; exact: nbhs_infty_ge.
apply: le_lt_trans (hclose _ _ (uniform_partition_is N hab) (uniform_partition_is n hab)
  (uniform_partition_mesh (hN N (leqnn N))) (uniform_partition_mesh (hN n hn))) _.
by lra.
Unshelve. all: end_near.
Qed.

(** Source for [uniform_sums_cvg]: the uniform sums converge to the
    integral, Federer 2.5.17, p. 111, by completeness of the real
    line. *)
Lemma uniform_sums_cvg (f : R -> R) (a b : R) :
  continuous f -> a <= b -> uniform_sums f a b @ \oo --> stieltjes_integral f a b.
Proof. by move=> hf hab; exact: (cauchy_cvg _ (uniform_sums_cauchy hf hab)). Qed.

(** Source for [eventually_threshold]: supporting extraction of a
    threshold from a property holding eventually, Federer 2.5.17,
    p. 111. *)
Lemma eventually_threshold (P : nat -> Prop) :
  (\forall n \near \oo, P n) -> exists N, forall n, (N <= n)%N -> P n.
Proof. by move=> [N _ hN]; exists N=> n hn; exact: hN. Qed.

(** Source for [stieltjes_integral_limit]: the sums converge, as delta
    tends to 0+, to int_a^b f dg, Federer 2.5.17, p. 111: every sum with
    mesh below a suitable delta is within e of the integral. *)
Theorem stieltjes_integral_limit (f : R -> R) (a b e : R) :
  continuous f -> a <= b -> 0 < e ->
  exists d, 0 < d /\ forall w, is_tagged_partition a b w -> tagged_mesh_lt d w ->
    `|stieltjes_sum f g w - stieltjes_integral f a b| < e.
Proof.
move=> hf hab he.
have he2 : 0 < e / 2 by lra.
have [d [hd hclose]] := fine_partitions_close hf hab he2.
exists d; split=> // w hw hm.
have hcv := uniform_sums_cvg hf hab.
have hnear : \forall n \near \oo, `|stieltjes_integral f a b - uniform_sums f a b n| < e / 2.
  have hb0 : \oo (uniform_sums f a b @^-1` ball (stieltjes_integral f a b) (e / 2)).
    by exact ((cvg_ballP _ _).1 hcv (e / 2) he2).
  by move: hb0; apply: filterS=> n /=; rewrite /ball /=.
have [N1 hN1] := eventually_threshold hnear.
have [N2 hN2] := uniform_mesh_small hab hd.
pose n := maxn N1 N2.
have h1 := hN1 n (leq_maxl N1 N2).
have h2 := uniform_partition_mesh (hN2 n (leq_maxr N1 N2)).
have h3 := hclose _ _ hw (uniform_partition_is n hab) hm h2.
apply: le_lt_trans (ler_distD (uniform_sums f a b n) _ _) _.
rewrite distrC in h1; rewrite (splitr e).
exact (ler_ltD h3 h1).
Qed.

(** Source for [stieltjes_integral_unique]: a real number approached by
    all sums with small mesh is int_a^b f dg, Federer 2.5.17, p. 111. *)
Theorem stieltjes_integral_unique (f : R -> R) (a b J : R) :
  continuous f -> a <= b ->
  (forall e, 0 < e -> exists d, 0 < d /\ forall w, is_tagged_partition a b w ->
     tagged_mesh_lt d w -> `|stieltjes_sum f g w - J| < e) ->
  J = stieltjes_integral f a b.
Proof.
move=> hf hab hJ; apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he2 : 0 < e / 2 by lra.
have [d1 [hd1 h1]] := hJ _ he2.
have [d2 [hd2 h2]] := stieltjes_integral_limit hf hab he2.
have hdm : 0 < Order.min d1 d2 by rewrite lt_min hd1 hd2.
have [N hN] := uniform_mesh_small hab hdm.
have hw := uniform_partition_is N hab.
have hm := uniform_partition_mesh (hN N (leqnn N)).
have hmin1 : Order.min d1 d2 <= d1 by rewrite ge_min lexx.
have hmin2 : Order.min d1 d2 <= d2 by rewrite ge_min lexx orbT.
have hm1 := tagged_mesh_lt_le hmin1 hm.
have hm2 := tagged_mesh_lt_le hmin2 hm.
have h1' := h1 _ hw hm1; rewrite distrC in h1'.
have h2' := h2 _ hw hm2.
apply: ltW; apply: le_lt_trans (ler_distD (stieltjes_sum f g (uniform_partition a b N)) _ _) _.
by rewrite (splitr e); exact (ltrD h1' h2').
Qed.

(** Source for [stieltjes_sum_add]: the sums are additive in f, Federer
    2.5.17, p. 111. *)
Lemma stieltjes_sum_add (f1 f2 : R -> R) (w : seq R) :
  stieltjes_sum (fun x => f1 x + f2 x) g w = stieltjes_sum f1 g w + stieltjes_sum f2 g w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize.
- by rewrite /= addr0.
- by rewrite /= addr0.
- by rewrite /= addr0.
- rewrite !stieltjes_sum_cons ih; last by move: hsize; rewrite /= ltnS; exact: ltnW.
  by ring.
Qed.

(** Source for [stieltjes_sum_scale]: the sums are homogeneous in f,
    Federer 2.5.17, p. 111. *)
Lemma stieltjes_sum_scale (c : R) (f : R -> R) (w : seq R) :
  stieltjes_sum (fun x => c * f x) g w = c * stieltjes_sum f g w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize.
- by rewrite /= mulr0.
- by rewrite /= mulr0.
- by rewrite /= mulr0.
- rewrite !stieltjes_sum_cons ih; last by move: hsize; rewrite /= ltnS; exact: ltnW.
  by ring.
Qed.

(** Source for [stieltjes_integral_add]: the integral is additive in f,
    Federer 2.5.17, p. 111, "linear with respect to f". *)
Theorem stieltjes_integral_add (f1 f2 : R -> R) (a b : R) :
  continuous f1 -> continuous f2 -> continuous (fun x => f1 x + f2 x) -> a <= b ->
  stieltjes_integral (fun x => f1 x + f2 x) a b =
    stieltjes_integral f1 a b + stieltjes_integral f2 a b.
Proof.
move=> hf1 hf2 hf hab; symmetry; apply: stieltjes_integral_unique=> // e he.
have he2 : 0 < e / 2 by lra.
have [d1 [hd1 h1]] := stieltjes_integral_limit hf1 hab he2.
have [d2 [hd2 h2]] := stieltjes_integral_limit hf2 hab he2.
exists (Order.min d1 d2); split; first by rewrite lt_min hd1 hd2.
move=> w hw hm.
have hmin1 : Order.min d1 d2 <= d1 by rewrite ge_min lexx.
have hmin2 : Order.min d1 d2 <= d2 by rewrite ge_min lexx orbT.
have e1 := h1 _ hw (tagged_mesh_lt_le hmin1 hm).
have e2 := h2 _ hw (tagged_mesh_lt_le hmin2 hm).
rewrite stieltjes_sum_add.
have -> : stieltjes_sum f1 g w + stieltjes_sum f2 g w
    - (stieltjes_integral f1 a b + stieltjes_integral f2 a b)
  = (stieltjes_sum f1 g w - stieltjes_integral f1 a b)
    + (stieltjes_sum f2 g w - stieltjes_integral f2 a b) by ring.
by apply: le_lt_trans (ler_normD _ _) _; rewrite (splitr e); exact (ltrD e1 e2).
Qed.

(** Source for [stieltjes_integral_scale]: the integral is homogeneous
    in f, Federer 2.5.17, p. 111. *)
Theorem stieltjes_integral_scale (c : R) (f : R -> R) (a b : R) :
  continuous f -> continuous (fun x => c * f x) -> a <= b ->
  stieltjes_integral (fun x => c * f x) a b = c * stieltjes_integral f a b.
Proof.
move=> hf hcf hab; symmetry; apply: stieltjes_integral_unique=> // e he.
have hc1 : 0 < `|c| + 1 by have := normr_ge0 c; lra.
have he' : 0 < e / (`|c| + 1) by rewrite divr_gt0.
have [d [hd h]] := stieltjes_integral_limit hf hab he'.
exists d; split=> // w hw hm.
have := h _ hw hm; rewrite stieltjes_sum_scale -mulrBr normrM ltr_pdivlMr // => hlt.
apply: le_lt_trans _ hlt; rewrite mulrC; apply: ler_wpM2l; first exact: normr_ge0.
by rewrite lerDl ler01.
Qed.

(** Source for [tagged_points_head0]: the first point is a, Federer
    2.5.17, p. 110. *)
Lemma tagged_points_head0 (a b : R) (w : seq R) :
  is_tagged_partition a b w -> head 0 (tagged_points w) = a.
Proof.
move=> hw; have hh := tagged_partition_head0 hw.
case: w hw hh=> [[_ [h _]]|t w _ /= ->] //; exact: tagged_points_head.
Qed.

(** Source for [tagged_points_last0]: the last point is b, Federer
    2.5.17, p. 110. *)
Lemma tagged_points_last0 (a b : R) (w : seq R) :
  is_tagged_partition a b w -> last 0 (tagged_points w) = b.
Proof.
move=> hw; apply: sorted_last_eq.
- exact (tagged_points_sorted hw.1).
- exact (tagged_partition_b_mem hw).
- by move=> x hx; have /andP[_] := tagged_partition_points_bounds hw hx.
Qed.

(** Source for [tagged_points_cons_exists]: the points of a nonempty
    sequence begin with its first term, Federer 2.5.17, p. 110. *)
Lemma tagged_points_cons_exists (t : R) (w : seq R) : exists ps, tagged_points (t :: w) = t :: ps.
Proof. by case: w=> [|u w]; [exists [::]|exists (tagged_points w)]. Qed.

(** Source for [stieltjes_sum_bound]: the sums are bounded by
    sup{|f(x)| : a <= x <= b} times the absolute increment sum of g over
    the points, Federer 2.5.17, p. 111. *)
Lemma stieltjes_sum_bound (f : R -> R) (M a b : R) (w : seq R) :
  is_tagged_partition a b w -> (forall x, a <= x <= b -> `|f x| <= M) ->
  `|stieltjes_sum f g w| <= M * absolute_chain g (tagged_points w).
Proof.
have [n] := ubnP (size w); elim: n w a=> // n ih w a hsize hw hM.
have hab : a <= b.
  by have /andP[_] := tagged_partition_points_bounds hw (tagged_partition_a_mem hw).
case: w hsize hw=> [|t [|u [|t' rest]]] hsize hw.
- by case: hw=> [_ [h _]].
- by rewrite /= normr0 mulr0.
- by case: hw=> [_ [h _]].
- have [t'' [rest' [hrest [hat [htu [hut' hw']]]]]] := tagged_partition_tail hw.
  case: hrest=> ht'' hrest'; subst t'' rest'.
  have ht'b : t' <= b.
    by have /andP[_] := tagged_partition_points_bounds hw' (tagged_partition_a_mem hw').
  have hu : a <= u <= b by rewrite hat htu /= (le_trans hut' ht'b).
  have hsize' : (size (t' :: rest) < n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  have hM' : forall x, t' <= x <= b -> `|f x| <= M.
    move=> x /andP[h1 h2]; apply: hM; rewrite h2 andbT; apply: le_trans h1.
    by rewrite hat (le_trans htu hut').
  have hih := ih _ _ hsize' hw' hM'.
  have [ps hps] := tagged_points_cons_exists t' rest.
  rewrite stieltjes_sum_cons tagged_points_cons hps absolute_chain_cons2 -hps.
  apply: le_trans (ler_normD _ _) _; rewrite (mulrDr M); apply: lerD=> //.
  by rewrite normrM; exact (ler_wpM2r (normr_ge0 _) (hM _ hu)).
Qed.

(** Source for [stieltjes_integral_bound]: the inequality
    |int_a^b f dg| <= sup{|f(x)| : a <= x <= b} V_a^b g of Federer
    2.5.17, p. 111, for every bound M of |f| on [a, b]. *)
Theorem stieltjes_integral_bound (f : R -> R) (a b M : R) :
  continuous f -> a <= b -> (forall x, a <= x <= b -> `|f x| <= M) ->
  `|stieltjes_integral f a b| <= M * total_variation a b.
Proof.
move=> hf hab hM; apply/ler_addgt0Pr=> e he.
have hM0 : 0 <= M by apply: le_trans (normr_ge0 (f a)) _; apply: hM; rewrite lexx hab.
have [d [hd hlim]] := stieltjes_integral_limit hf hab he.
have [N hN] := uniform_mesh_small hab hd.
have hw := uniform_partition_is N hab.
have h1 := hlim _ hw (uniform_partition_mesh (hN N (leqnn N))).
have h2 := stieltjes_sum_bound hw hM.
have hne : tagged_points (uniform_partition a b N) <> [::].
  by move=> h; have := tagged_partition_a_mem hw; rewrite h.
have h3 : absolute_chain g (tagged_points (uniform_partition a b N)) <= total_variation a b.
  exact (absolute_chain_le_variation hab (tagged_points_sorted hw.1) (tagged_points_head0 hw)
    (tagged_points_last0 hw) hne).
rewrite -[stieltjes_integral f a b](subrK (stieltjes_sum f g (uniform_partition a b N))).
apply: le_trans (ler_normD _ _) _; rewrite addrC; apply: lerD.
- exact (le_trans h2 (ler_wpM2l hM0 h3)).
- by rewrite distrC; exact (ltW h1).
Qed.

(** Source for [stieltjes_sum_cat]: the sum over the junction of a
    sequence from a to b and a sequence from b to c is the sum of the
    two sums, Federer 2.5.17, p. 111. *)
Lemma stieltjes_sum_cat (f : R -> R) (w1 w2 : seq R) :
  odd (size w1) -> last 0 w1 = head 0 w2 -> w2 <> [::] ->
  stieltjes_sum f g (w1 ++ behead w2) = stieltjes_sum f g w1 + stieltjes_sum f g w2.
Proof.
have [n] := ubnP (size w1); elim: n w1=> // n ih [|t [|u [|t' rest]]] hsize hodd hl hne //.
- by case: w2 hl hne ih=> [//|t2 w2] /= -> _ _; rewrite /= add0r.
- have hsize' : (size (t' :: rest) < n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  have hodd' : odd (size (t' :: rest)) by move: hodd; rewrite /= negbK.
  rewrite !cat_cons stieltjes_sum_cons -cat_cons (ih _ hsize' hodd' hl hne) stieltjes_sum_cons.
  by ring.
Qed.

(** Source for [tagged_partition_cat]: the junction of a sequence from a
    to b and a sequence from b to c is a sequence from a to c, Federer
    2.5.17, p. 111. *)
Lemma tagged_partition_cat (a b c : R) (w1 w2 : seq R) :
  is_tagged_partition a b w1 -> is_tagged_partition b c w2 ->
  is_tagged_partition a c (w1 ++ behead w2).
Proof.
move=> hw1 hw2.
have [hs1 [ho1 [hh1 hl1]]] := hw1.
have [hs2 [ho2 [hh2 hl2]]] := hw2.
case: w2 hw2 hs2 ho2 hh2 hl2=> [|t2 w2] hw2 hs2 ho2 hh2 hl2; first by [].
move: hh2=> /= ht2; subst t2.
have hw1ne : w1 <> [::] by move=> h; rewrite h in ho1.
have hall1 : forall x, x \in w1 -> x <= b.
  by move=> x hx; rewrite -(tagged_partition_last0 hw1); exact: (sorted_le_last 0 hs1 hx).
have hall2 : forall y, y \in w2 -> b <= y.
  by move=> y hy; have := order_path_min le_trans hs2; move/allP; exact.
split; last split; last split.
- rewrite /=; apply: sorted_cat_le=> //; first exact (path_sorted hs2).
  by move=> x y hx hy; exact (le_trans (hall1 x hx) (hall2 y hy)).
- by rewrite /= size_cat oddD ho1 /=; move: ho2; rewrite /=.
- by case: w1 hw1ne hh1 {hw1 hs1 ho1 hl1 hall1}=> [//|t1 w1'] _ /= ->.
- by rewrite /= last_cat hl1; move: hl2; rewrite /=.
Qed.

(** Source for [tagged_mesh_lt_cat]: the junction of two sequences with
    mesh below delta has mesh below delta, Federer 2.5.17, p. 111. *)
Lemma tagged_mesh_lt_cat (d : R) (w1 w2 : seq R) :
  odd (size w1) -> last 0 w1 = head 0 w2 ->
  tagged_mesh_lt d w1 -> tagged_mesh_lt d w2 -> tagged_mesh_lt d (w1 ++ behead w2).
Proof.
have [n] := ubnP (size w1); elim: n w1=> // n ih [|t [|u [|t' rest]]] hsize hodd hl hm1 hm2 //.
- by case: w2 hl hm2 ih=> [//|t2 w2] /= -> hm2 _.
- have hsize' : (size (t' :: rest) < n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  have hodd' : odd (size (t' :: rest)) by move: hodd; rewrite /= negbK.
  move: hm1; rewrite !cat_cons !tagged_mesh_lt_cons=> /andP[-> hm1]; rewrite andTb.
  by rewrite -cat_cons; exact (ih _ hsize' hodd' hl hm1 hm2).
Qed.

(** Source for [stieltjes_integral_cat]: int_a^b f dg + int_b^c f dg
    = int_a^c f dg whenever a <= b <= c, Federer 2.5.17, p. 111, by
    the junctions of uniform sequences of [a, b] and [b, c]. *)
Theorem stieltjes_integral_cat (f : R -> R) (a b c : R) :
  continuous f -> a <= b -> b <= c ->
  stieltjes_integral f a b + stieltjes_integral f b c = stieltjes_integral f a c.
Proof.
move=> hf hab hbc; have hac := le_trans hab hbc.
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he3 : 0 < e / 3 by lra.
have [d [hd h]] := stieltjes_integral_limit hf hac he3.
have [d1 [hd1 h1]] := stieltjes_integral_limit hf hab he3.
have [d2 [hd2 h2]] := stieltjes_integral_limit hf hbc he3.
pose dm := Order.min d (Order.min d1 d2).
have hdm : 0 < dm by rewrite /dm !lt_min hd hd1 hd2.
have hdmd : dm <= d by rewrite /dm ge_min lexx.
have hdm1 : dm <= d1 by rewrite /dm ge_min [X in _ || X]ge_min lexx orTb orbT.
have hdm2 : dm <= d2 by rewrite /dm ge_min [X in _ || X]ge_min lexx !orbT.
have [N1 hN1] := uniform_mesh_small hab hdm.
have [N2 hN2] := uniform_mesh_small hbc hdm.
pose n := maxn N1 N2.
have hw1 := uniform_partition_is n hab.
have hw2 := uniform_partition_is n hbc.
have hm1 := uniform_partition_mesh (hN1 n (leq_maxl N1 N2)).
have hm2 := uniform_partition_mesh (hN2 n (leq_maxr N1 N2)).
have hlh : last 0 (uniform_partition a b n) = head 0 (uniform_partition b c n).
  by rewrite (tagged_partition_last0 hw1) (tagged_partition_head0 hw2).
have hne2 : uniform_partition b c n <> [::].
  by move=> hh; have := tagged_partition_a_mem hw2; rewrite hh.
have hw := tagged_partition_cat hw1 hw2.
have hm := tagged_mesh_lt_cat hw1.2.1 hlh hm1 hm2.
have hS := stieltjes_sum_cat f hw1.2.1 hlh hne2.
have e0 := h _ hw (tagged_mesh_lt_le hdmd hm).
have e1 := h1 _ hw1 (tagged_mesh_lt_le hdm1 hm1).
have e2 := h2 _ hw2 (tagged_mesh_lt_le hdm2 hm2).
rewrite hS in e0.
have -> : stieltjes_integral f a b + stieltjes_integral f b c - stieltjes_integral f a c
  = (stieltjes_integral f a b - stieltjes_sum f g (uniform_partition a b n))
    + (stieltjes_integral f b c - stieltjes_sum f g (uniform_partition b c n))
    + (stieltjes_sum f g (uniform_partition a b n) + stieltjes_sum f g (uniform_partition b c n)
       - stieltjes_integral f a c) by ring.
apply: ltW; apply: le_lt_trans (ler_normD _ _) _.
have -> : e = e / 3 + e / 3 + e / 3 by lra.
apply: ltrD _ e0; apply: le_lt_trans (ler_normD _ _) _.
by rewrite distrC [X in _ + X]distrC; exact (ltrD e1 e2).
Qed.

End StieltjesIntegral.
