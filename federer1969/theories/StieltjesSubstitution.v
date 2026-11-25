(** Federer (1969), 2.5.18(2), p. 112: if f, g, h map R into R, f and g are
    continuous, g is increasing, -oo < a < b < oo and V_{g(a)}^{g(b)} h <
    oo, then int_a^b (f o g) d(h o g) = int_{g(a)}^{g(b)} f dh, because both
    integrals are limits of the sums sum_j f[g(u_j)] (h[g(t_{j+1})] -
    h[g(t_j)]). The integrals are those of 2.5.17. The monotonicity
    hypothesis is used only in the weak form that g is nondecreasing. The
    sums for h o g over a sequence from a to b are the sums for h over the
    image sequence from g(a) to g(b), whose mesh is controlled by the
    uniform continuity of g on the segment. The printed hypothesis concerns
    the variation of h on [g(a), g(b)] only; it is reduced to finite
    variation on every segment by composing h with the retraction of R onto
    [g(a), g(b)]. The final remark on the image g_# of the induced measures
    is not formalised here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground ExtendedRealBounds CurveVariationUP
  CurveArcLength SegmentUniformContinuity StieltjesSums StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Substitution.
Variable R : realType.

(** Source for [stieltjes_sum_comp]: the sum of f o g against h o g over
    a sequence equals the sum of f against h over the image sequence,
    Federer 2.5.18(2), p. 112. *)
Lemma stieltjes_sum_comp (f h g : R -> R) (w : seq R) :
  stieltjes_sum (f \o g) (h \o g) w = stieltjes_sum f h (map g w).
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize //.
rewrite !map_cons !stieltjes_sum_cons -map_cons ih //.
by move: hsize; rewrite /= ltnS; exact: ltnW.
Qed.

(** Source for [stieltjes_sum_eq_on]: the sum depends only on the values
    of the integrator at the terms of the sequence, Federer 2.5.17,
    p. 110, used in 2.5.18(2), p. 112. *)
Lemma stieltjes_sum_eq_on (f g1 g2 : R -> R) (w : seq R) :
  (forall x, x \in w -> g1 x = g2 x) -> stieltjes_sum f g1 w = stieltjes_sum f g2 w.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize heq //.
have ht : t \in t :: u :: t' :: rest by rewrite !inE eqxx.
have ht' : t' \in t :: u :: t' :: rest by rewrite !inE eqxx /= ?orbT.
rewrite !stieltjes_sum_cons (heq t ht) (heq t' ht'); congr (_ + _); apply: ih.
- by move: hsize; rewrite /= ltnS; exact: ltnW.
- by move=> x hx; apply: heq; rewrite 2!inE hx !orbT.
Qed.

(** Source for [tagged_partition_mem_bounds]: every term of a sequence
    from a to b lies in [a, b], Federer 2.5.17, p. 110. *)
Lemma tagged_partition_mem_bounds (a b : R) (w : seq R) (x : R) :
  is_tagged_partition a b w -> x \in w -> a <= x <= b.
Proof.
move=> hw hx; have := sorted_mem_bounds hw.1 hx.
by rewrite (tagged_partition_head0 hw) (tagged_partition_last0 hw).
Qed.

(** Source for [stieltjes_integral_eq_on]: the integral over [a, b]
    depends only on the values of the integrator on [a, b], Federer
    2.5.17, p. 111, used in 2.5.18(2), p. 112. *)
Lemma stieltjes_integral_eq_on (f g1 g2 : R -> R) (a b : R) :
  a <= b -> (forall x, a <= x <= b -> g1 x = g2 x) ->
  stieltjes_integral g1 f a b = stieltjes_integral g2 f a b.
Proof.
move=> hab heq; rewrite /stieltjes_integral.
have -> // : uniform_sums g1 f a b = uniform_sums g2 f a b.
apply/funext=> n; rewrite /uniform_sums; apply: stieltjes_sum_eq_on=> x hx.
exact: heq (tagged_partition_mem_bounds (uniform_partition_is n hab) hx).
Qed.

(** Source for [tagged_partition_map]: a nondecreasing map sends a
    sequence from a to b to a sequence from g(a) to g(b), Federer
    2.5.18(2), p. 112. *)
Lemma tagged_partition_map (g : R -> R) (a b : R) (w : seq R) :
  (forall x y, x <= y -> g x <= g y) -> is_tagged_partition a b w ->
  is_tagged_partition (g a) (g b) (map g w).
Proof.
move=> hmono [hs [hodd [hh hl]]]; split; first exact: (homo_sorted hmono w hs).
split; first by rewrite size_map.
split; last by rewrite last_map hl.
by case: w hh {hs hodd hl}=> [|t w'] //= ->.
Qed.

(** Source for [variation_partition_map]: a nondecreasing map sends a
    partition of [c, d] to a partition of [g(c), g(d)], Federer 2.5.16,
    p. 109, used in 2.5.18(2), p. 112. *)
Lemma variation_partition_map (g : R -> R) (c d : R) (s : seq R) :
  (forall x y, x <= y -> g x <= g y) -> is_variation_partition c d s ->
  is_variation_partition (g c) (g d) (map g s).
Proof.
move=> hmono [hs [hsize [hh hl]]]; split; first exact: (homo_sorted hmono s hs).
split; first by rewrite size_map.
split; last by rewrite last_map hl.
by case: s hh {hs hsize hl}=> [|t s'] //= ->.
Qed.

(** Source for [tagged_mesh_lt_map]: the image sequence has small mesh
    when the map has small increments on the terms, Federer 2.5.18(2),
    p. 112. *)
Lemma tagged_mesh_lt_map (g : R -> R) (d d' : R) (w : seq R) :
  (forall x y, x \in w -> y \in w -> x <= y -> y - x < d -> g y - g x < d') ->
  sorted <=%O w -> tagged_mesh_lt d w -> tagged_mesh_lt d' (map g w).
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize hg hs //.
rewrite !map_cons !tagged_mesh_lt_cons -map_cons=> /andP[h1 h2].
have ht : t \in t :: u :: t' :: rest by rewrite !inE eqxx.
have ht' : t' \in t :: u :: t' :: rest by rewrite !inE eqxx /= ?orbT.
have htu : t <= u by move: hs=> /= /andP[].
have hut' : u <= t' by move: hs=> /= /andP[_ /andP[]].
apply/andP; split; first exact: hg ht ht' (le_trans htu hut') h1.
apply: ih=> //.
- by move: hsize; rewrite /= ltnS; exact: ltnW.
- by move=> x y hx hy hxy hd'; apply: hg=> //; rewrite 2!inE ?hx ?hy !orbT.
- by move: hs=> /= /andP[_ /andP[_ h3]]; exact: h3.
Qed.

(** Source for [chain_sum_comp]: the chain sum of h o g over a sequence
    is the chain sum of h over the image sequence, Federer 2.5.16,
    p. 109, used in 2.5.18(2), p. 112. *)
Lemma chain_sum_comp (h g : R -> R) (s : seq R) :
  chain_sum (h \o g : R -> real_line_metric R) s
  = chain_sum (h : R -> real_line_metric R) (map g s).
Proof.
have [n] := ubnP (size s); elim: n s=> // n ih [|t [|u rest]] hsize //.
by rewrite !map_cons !chain_sum_cons -map_cons ih //; move: hsize; rewrite /= ltnS.
Qed.

(** Source for [curve_variation_comp_le]: the variation of h o g on
    [c, d] is at most the variation of h on [g(c), g(d)] for nondecreasing
    g, Federer 2.5.16, p. 109, used in 2.5.18(2), p. 112. *)
Lemma curve_variation_comp_le (h g : R -> R) (c d : R) :
  (forall x y, x <= y -> g x <= g y) -> c <= d ->
  (curve_variation (h \o g : R -> real_line_metric R) c d
    <= curve_variation (h : R -> real_line_metric R) (g c) (g d))%E.
Proof.
move=> hmono hcd; apply: extended_real_sup_least=> v [s [hs ->]].
rewrite chain_sum_comp; apply: extended_real_sup_upper.
by exists (map g s); split; first exact: variation_partition_map hmono hs.
Qed.

(** Source for [stieltjes_substitution]: the formula
    int_a^b (f o g) d(h o g) = int_{g(a)}^{g(b)} f dh of Federer
    2.5.18(2), p. 112, for h of finite variation on every segment. *)
Theorem stieltjes_substitution (f g h : R -> R) (a b : R) :
  continuous f -> continuous g -> (forall x y, x <= y -> g x <= g y) ->
  curve_locally_finite_variation (h : R -> real_line_metric R) -> a <= b ->
  stieltjes_integral (h \o g) (f \o g) a b = stieltjes_integral h f (g a) (g b).
Proof.
move=> hf hgc hmono hh hab.
have hgab : g a <= g b := hmono _ _ hab.
have hhg : curve_locally_finite_variation (h \o g : R -> real_line_metric R).
  move=> c d hcd; apply: le_lt_trans (curve_variation_comp_le h hmono hcd) _.
  exact: hh (hmono _ _ hcd).
have hfg : continuous (f \o g).
  by move=> x; apply: continuous_comp; [exact: hgc | exact: hf].
apply/esym; apply: (stieltjes_integral_unique hhg hfg hab)=> e he.
have [d [hd hlim]] := stieltjes_integral_limit hh hf hgab he.
have [d0 [hd0 hunif]] := segment_uniform_continuity a b hgc hd.
exists d0; split=> // w hw hm.
rewrite stieltjes_sum_comp.
apply: hlim; first exact: tagged_partition_map hmono hw.
apply: tagged_mesh_lt_map hm; last by case: hw.
move=> x y hx hy hxy hd'.
have hxb := tagged_partition_mem_bounds hw hx.
have hyb := tagged_partition_mem_bounds hw hy.
have hn : `|y - x| < d0 by rewrite ger0_norm ?subr_ge0.
exact: le_lt_trans (ler_norm _) (hunif y x hyb hxb hn).
Qed.

(** Source for [segment_retraction]: the nondecreasing retraction of R
    onto [c, d], used to reduce the printed hypothesis of Federer
    2.5.18(2), p. 112, to finite variation on every segment. *)
Definition segment_retraction (c d t : R) : R := Order.max c (Order.min t d).

(** Source for [segment_retraction_monotone]: the retraction is
    nondecreasing, Federer 2.5.18(2), p. 112. *)
Lemma segment_retraction_monotone (c d x y : R) :
  x <= y -> segment_retraction c d x <= segment_retraction c d y.
Proof.
move=> hxy; rewrite /segment_retraction ge_max le_max lexx /= le_max; apply/orP; right.
by rewrite le_min !ge_min hxy lexx orbT.
Qed.

(** Source for [segment_retraction_id]: the retraction fixes [c, d],
    Federer 2.5.18(2), p. 112. *)
Lemma segment_retraction_id (c d t : R) : c <= t <= d -> segment_retraction c d t = t.
Proof. by move=> /andP[h1 h2]; rewrite /segment_retraction min_l // max_r. Qed.

(** Source for [segment_retraction_bounds]: the retraction takes values
    in [c, d], Federer 2.5.18(2), p. 112. *)
Lemma segment_retraction_bounds (c d t : R) : c <= d -> c <= segment_retraction c d t <= d.
Proof.
move=> hcd; rewrite /segment_retraction; apply/andP; split; first by rewrite le_max lexx.
by rewrite ge_max hcd /= ge_min lexx orbT.
Qed.

(** Source for [stieltjes_substitution_segment]: the formula of Federer
    2.5.18(2), p. 112. *)
Theorem stieltjes_substitution_segment (f g h : R -> R) (a b : R) :
  continuous f -> continuous g -> (forall x y, x <= y -> g x <= g y) -> a <= b ->
  (curve_variation (h : R -> real_line_metric R) (g a) (g b) < +oo)%E ->
  stieltjes_integral (h \o g) (f \o g) a b = stieltjes_integral h f (g a) (g b).
Proof.
move=> hf hgc hmono hab hV.
have hgab : g a <= g b := hmono _ _ hab.
pose c := segment_retraction (g a) (g b).
have hcmono : forall x y, x <= y -> c x <= c y := segment_retraction_monotone (g a) (g b).
have hc : curve_locally_finite_variation (h \o c : R -> real_line_metric R).
  move=> x y hxy; apply: le_lt_trans (curve_variation_comp_le h hcmono hxy) _.
  apply: le_lt_trans _ hV; apply: curve_variation_monotone.
  - by have /andP[] := segment_retraction_bounds x hgab.
  - exact: hcmono.
  - by have /andP[_] := segment_retraction_bounds y hgab.
have hleft : stieltjes_integral (h \o g) (f \o g) a b
    = stieltjes_integral ((h \o c) \o g) (f \o g) a b.
  apply: stieltjes_integral_eq_on hab _ => x /andP[hax hxb] /=.
  by rewrite /c segment_retraction_id // (hmono _ _ hax) (hmono _ _ hxb).
have hright : stieltjes_integral h f (g a) (g b) = stieltjes_integral (h \o c) f (g a) (g b).
  by apply: stieltjes_integral_eq_on hgab _ => x hx /=; rewrite /c segment_retraction_id.
by rewrite hleft hright; exact: stieltjes_substitution hf hgc hmono hc hab.
Qed.

End Substitution.
