(** Federer (1969), 2.5.16, p. 110: if Y is a Banach space with a norm
    inducing p, then G extends to a Lipschitzian map H : R -> Y with Lip(H)
    = Lip(G), by defining H[lambda s(x-) + (1 - lambda) s(x)] = lambda g(x-)
    + (1 - lambda) g(x), H[lambda s(x) + (1 - lambda) s(x+)] = lambda g(x) +
    (1 - lambda) g(x+) whenever x in R and 0 <= lambda <= 1, and H(z) =
    g(-oo) whenever -oo < z <= inf im s, H(z) = g(oo) whenever sup im s <= z
    < oo. Here Y is a real vector space normed by nu in the sense of 1.10.5
    with the metric of 2.2.7, complete in the sense of 2.2.8. The map H is
    specified by the predicate [is_curve_banach_extension], which records
    the printed formulas, H o s = g and the equality of the Lipschitz
    constants; existence is proved through the interpolation of
    CurveBanachExtensionInterpolation.v applied to G on im s, and uniqueness
    from the printed formulas alone, every real number lying in im s, in one
    of the closed intervals of the formulas, or beyond inf im s or sup im s. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP CurveVariationUP CurveArcLength
  CurveOneSidedLimits CurveInfiniteLimits CurveLipschitzFactor CurveBanachExtensionInterpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurveBanachExtensionUP.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Local Notation Y := (real_norm_metric_space hN).

(** Source for [is_curve_banach_extension]: the map H of Federer 2.5.16,
    p. 110: H o s = g, the two printed interpolation formulas on the
    intervals between s(x-), s(x) and s(x+), the values g(-oo) below
    inf im s and g(oo) above sup im s, and Lip(H) <= L whenever
    p[g(t), g(u)] <= L |s(t) - s(u)| for all t, u, that is whenever
    Lip(G) <= L. *)
Record is_curve_banach_extension (g H : R -> Y) : Prop := {
  curve_banach_compose : forall t, H (arc_length g t) = g t;
  curve_banach_left : forall x (y : Y), g @ x^'- --> y -> forall l, 0 <= l <= 1 ->
    H (l * arc_length_left g x + (1 - l) * arc_length g x) = l *: y + (1 - l) *: g x;
  curve_banach_right : forall x (y : Y), g @ x^'+ --> y -> forall l, 0 <= l <= 1 ->
    H (l * arc_length g x + (1 - l) * arc_length_right g x) = l *: g x + (1 - l) *: y;
  curve_banach_ninfty : forall y : Y, g @ -oo --> y ->
    forall z, (forall t, z <= arc_length g t) -> H z = y;
  curve_banach_pinfty : forall y : Y, g @ +oo --> y ->
    forall z, (forall t, arc_length g t <= z) -> H z = y;
  curve_banach_lipschitz : forall L, 0 <= L ->
    (forall t u, mdist (g t) (g u) <= L * `|arc_length g t - arc_length g u|) ->
    forall z w, mdist (H z) (H w) <= L * `|z - w|
}.

End CurveBanachExtensionUP.

Section CurveBanachExtension.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Local Notation Y := (real_norm_metric_space hN).
Hypothesis hY : is_complete_metric_space Y.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Local Notation s := (arc_length g).
Local Notation sl := (arc_length_left g).
Local Notation sr := (arc_length_right g).
Local Notation G := (arc_length_factor g).

(** Source for [arc_length_left_closure]: s(x-) lies in the closure of
    im s, Federer 2.5.16, p. 109. *)
Lemma arc_length_left_closure (x : R) : closure (range s) (sl x).
Proof.
move=> B /nbhs_ballP [e he hball].
have he' : 0 < e := he.
have [t htx ht] := arc_length_left_adherent hfin x he'.
exists (s t); split; first by exists t.
apply: hball; have := arc_length_le_left hfin htx.
by rewrite /ball /= => hle; rewrite ger0_norm ?subr_ge0 //; lra.
Qed.

(** Source for [arc_length_right_closure]: s(x+) lies in the closure of
    im s, Federer 2.5.16, p. 109. *)
Lemma arc_length_right_closure (x : R) : closure (range s) (sr x).
Proof.
move=> B /nbhs_ballP [e he hball].
have he' : 0 < e := he.
have [t hxt ht] := arc_length_right_adherent hfin x he'.
exists (s t); split; first by exists t.
apply: hball; have := arc_length_right_le hfin hxt.
by rewrite /ball /= => hle; rewrite ler0_norm ?subr_le0 //; lra.
Qed.

(** Source for [arc_length_left_gap]: no value of s lies strictly
    between s(x-) and s(x), Federer 2.5.16, p. 109. *)
Lemma arc_length_left_gap (x : R) : forall u, sl x < u < s x -> ~ range s u.
Proof.
move=> u /andP[h1 h2] [t _ htu]; rewrite -htu in h1 h2.
case: (ltP t x)=> htx.
  by have := arc_length_le_left hfin htx; rewrite leNgt h1.
by have := arc_length_monotone hfin htx; rewrite leNgt h2.
Qed.

(** Source for [arc_length_right_gap]: no value of s lies strictly
    between s(x) and s(x+), Federer 2.5.16, p. 109. *)
Lemma arc_length_right_gap (x : R) : forall u, s x < u < sr x -> ~ range s u.
Proof.
move=> u /andP[h1 h2] [t _ htu]; rewrite -htu in h1 h2.
case: (leP t x)=> htx.
  by have := arc_length_monotone hfin htx; rewrite leNgt h1.
by have := arc_length_right_le hfin htx; rewrite leNgt h2.
Qed.

(** Source for [arc_length_factor_one_lipschitz]: G is 1 Lipschitzian
    on im s, Lip(G) <= 1 in Federer 2.5.16, p. 110. *)
Lemma arc_length_factor_one_lipschitz (u v : R) :
  range s u -> range s v -> mdist (G u) (G v) <= 1 * `|u - v|.
Proof. by move=> hu hv; rewrite mul1r; exact (arc_length_factor_lipschitz hfin hu hv). Qed.

Section Limits.
Variable H : R -> Y.
Hypothesis hcomp : forall t, H (s t) = g t.
Hypothesis hlip : forall z w, mdist (H z) (H w) <= `|z - w|.

(** Source for [extension_left_limit]: a 1 Lipschitzian map H with
    H o s = g satisfies H(s(x-)) = g(x-), Federer 2.5.16, p. 110. *)
Lemma extension_left_limit (x : R) (y : Y) : g @ x^'- --> y -> H (sl x) = y.
Proof.
move=> hy.
have hH : g @ x^'- --> H (sl x).
  apply/metricType_numDomainType.cvgrPdist_lt=> e he.
  have [t0 ht0x ht0] := arc_length_left_adherent hfin x he.
  near=> t.
  have ht0t : t0 <= t by near: t; exact: (nbhs_left_ge ht0x).
  have htx : t < x by near: t; exact: nbhs_left_lt.
  rewrite -hcomp; apply: le_lt_trans (hlip _ _) _.
  have h1 := arc_length_le_left hfin htx.
  have h2 := arc_length_monotone hfin ht0t.
  by rewrite ger0_norm ?subr_ge0 //; lra.
exact (esym (@cvg_unique Y (@metric_hausdorff _ Y) _ (fmap_proper_filter g (at_left_proper_filter x))
  _ _ hy hH)).
Unshelve. all: end_near.
Qed.

(** Source for [extension_right_limit]: H(s(x+)) = g(x+), Federer
    2.5.16, p. 110. *)
Lemma extension_right_limit (x : R) (y : Y) : g @ x^'+ --> y -> H (sr x) = y.
Proof.
move=> hy.
have hH : g @ x^'+ --> H (sr x).
  apply/metricType_numDomainType.cvgrPdist_lt=> e he.
  have [t0 hxt0 ht0] := arc_length_right_adherent hfin x he.
  near=> t.
  have htt0 : t <= t0 by near: t; exact: (nbhs_right_le hxt0).
  have hxt : x < t by near: t; exact: nbhs_right_gt.
  rewrite -hcomp; apply: le_lt_trans (hlip _ _) _.
  have h1 := arc_length_right_le hfin hxt.
  have h2 := arc_length_monotone hfin htt0.
  by rewrite ler0_norm ?subr_le0 //; lra.
exact (esym (@cvg_unique Y (@metric_hausdorff _ Y) _ (fmap_proper_filter g (at_right_proper_filter x))
  _ _ hy hH)).
Unshelve. all: end_near.
Qed.

(** Source for [extension_ninfty_limit]: H(inf im s) = g(-oo) when im s
    is bounded below, Federer 2.5.16, p. 110. *)
Lemma extension_ninfty_limit (y : Y) : has_lbound (range s) -> g @ -oo --> y -> H (inf (range s)) = y.
Proof.
move=> hlb hy.
have hne : range s !=set0 by exists (s 0), 0.
have hi : has_inf (range s) by split.
have hH : g @ -oo --> H (inf (range s)).
  apply/metricType_numDomainType.cvgrPdist_lt=> e he.
  have [_ [t0 _ <-] ht0] := inf_adherent he hi.
  near=> t.
  have htt0 : t <= t0 by near: t; exact: nbhs_ninfty_le (num_real t0).
  rewrite -hcomp; apply: le_lt_trans (hlip _ _) _.
  have h1 : inf (range s) <= s t by exact: (ge_inf hlb (ex_intro2 _ _ t I erefl)).
  have h2 := arc_length_monotone hfin htt0.
  by rewrite ler0_norm ?subr_le0 //; lra.
exact (esym (@cvg_unique Y (@metric_hausdorff _ Y) _ (fmap_proper_filter g proper_ninfty_nbhs)
  _ _ hy hH)).
Unshelve. all: end_near.
Qed.

(** Source for [extension_pinfty_limit]: H(sup im s) = g(oo) when im s
    is bounded above, Federer 2.5.16, p. 110. *)
Lemma extension_pinfty_limit (y : Y) : has_ubound (range s) -> g @ +oo --> y -> H (sup (range s)) = y.
Proof.
move=> hub hy.
have hne : range s !=set0 by exists (s 0), 0.
have hs : has_sup (range s) by split.
have hH : g @ +oo --> H (sup (range s)).
  apply/metricType_numDomainType.cvgrPdist_lt=> e he.
  have [_ [t0 _ <-] ht0] := sup_adherent he hs.
  near=> t.
  have ht0t : t0 <= t by near: t; exact: nbhs_pinfty_ge (num_real t0).
  rewrite -hcomp; apply: le_lt_trans (hlip _ _) _.
  have h1 : s t <= sup (range s) by exact: (sup_upper_bound hs (ex_intro2 _ _ t I erefl)).
  have h2 := arc_length_monotone hfin ht0t.
  by rewrite ger0_norm ?subr_ge0 //; lra.
exact (esym (@cvg_unique Y (@metric_hausdorff _ Y) _ (fmap_proper_filter g proper_pinfty_nbhs)
  _ _ hy hH)).
Unshelve. all: end_near.
Qed.

End Limits.

(** Source for [curve_banach_extension_exists]: existence of the map H of
    Federer 2.5.16, p. 110 *)
Theorem curve_banach_extension_exists : exists H : R -> Y, is_curve_banach_extension g H.
Proof.
have [H hH] := gap_interpolation_exists hY arc_length_factor_one_lipschitz.
have hcomp : forall t, H (s t) = g t.
  by move=> t; rewrite (gap_interpolation_extends hH (ex_intro2 _ _ t I erefl)) (arc_length_factor_compose hfin).
have hlip1 : forall z w, mdist (H z) (H w) <= `|z - w|.
  move=> z w; rewrite -[`|z - w|]mul1r; apply: (gap_interpolation_lipschitz hH ler01)=> u v hu hv.
  exact: arc_length_factor_one_lipschitz.
exists H; constructor=> //.
- move=> x y hy l hl.
  rewrite (gap_interpolation_affine hH (arc_length_left_le hfin x) (@arc_length_left_closure x)
    (subset_closure (ex_intro2 _ _ x I erefl)) (@arc_length_left_gap x) hl).
  by rewrite (extension_left_limit hcomp hlip1 hy) hcomp.
- move=> x y hy l hl.
  rewrite (gap_interpolation_affine hH (arc_length_right_ge hfin x)
    (subset_closure (ex_intro2 _ _ x I erefl)) (@arc_length_right_closure x) (@arc_length_right_gap x) hl).
  by rewrite (extension_right_limit hcomp hlip1 hy) hcomp.
- move=> y hy z hz.
  have hlb : has_lbound (range s) by exists z=> _ [t _ <-]; exact: hz.
  have hne : range s !=set0 by exists (s 0), 0.
  have hi : has_inf (range s) by split.
  have hcl : closure (range s) (inf (range s)).
    move=> B /nbhs_ballP [e he hball].
    have he' : 0 < e := he.
    have [_ [t _ <-] ht] := inf_adherent he' hi.
    exists (s t); split; first by exists t.
    apply: hball; have : inf (range s) <= s t by exact: (ge_inf hlb (ex_intro2 _ _ t I erefl)).
    by rewrite /ball /= => hle; rewrite ler0_norm ?subr_le0 //; lra.
  have hlow : forall u, range s u -> inf (range s) <= u by move=> u hu; exact: (ge_inf hlb hu).
  have hzi : z <= inf (range s) by apply: lb_le_inf hne _ => _ [t _ <-]; exact: hz.
  rewrite (gap_interpolation_below hH hcl hlow hzi).
  exact (extension_ninfty_limit hcomp hlip1 hlb hy).
- move=> y hy z hz.
  have hub : has_ubound (range s) by exists z=> _ [t _ <-]; exact: hz.
  have hne : range s !=set0 by exists (s 0), 0.
  have hs : has_sup (range s) by split.
  have hcl : closure (range s) (sup (range s)).
    move=> B /nbhs_ballP [e he hball].
    have he' : 0 < e := he.
    have [_ [t _ <-] ht] := sup_adherent he' hs.
    exists (s t); split; first by exists t.
    apply: hball; have : s t <= sup (range s) by exact: (sup_upper_bound hs (ex_intro2 _ _ t I erefl)).
    by rewrite /ball /= => hle; rewrite ger0_norm ?subr_ge0 //; lra.
  have hup : forall u, range s u -> u <= sup (range s) by move=> u hu; exact: (sup_upper_bound hs hu).
  have hsz : sup (range s) <= z by apply: ge_sup hne _ => _ [t _ <-]; exact: hz.
  rewrite (gap_interpolation_above hH hcl hup hsz).
  exact (extension_pinfty_limit hcomp hlip1 hub hy).
- move=> L hL hgL; apply: (gap_interpolation_lipschitz hH hL)=> _ _ [t _ <-] [u _ <-].
  by rewrite !(arc_length_factor_compose hfin); exact: hgL.
Qed.

(** Source for [curve_banach_extension_factor]: H extends G, Federer
    2.5.16, p. 110. *)
Lemma curve_banach_extension_factor (H : R -> Y) :
  is_curve_banach_extension g H -> forall z, range s z -> H z = G z.
Proof. by move=> hH z [t _ <-]; rewrite (curve_banach_compose hH) (arc_length_factor_compose hfin). Qed.

(** Source for [curve_banach_extension_lipschitz_iff]: Lip(H) = Lip(G),
    Federer 2.5.16, p. 110. *)
Theorem curve_banach_extension_lipschitz_iff (H : R -> Y) (L : R) :
  is_curve_banach_extension g H -> 0 <= L ->
  (forall z w, range s z -> range s w -> mdist (G z) (G w) <= L * `|z - w|) <->
  (forall z w, mdist (H z) (H w) <= L * `|z - w|).
Proof.
move=> hH hL; split=> hGL.
  apply: (curve_banach_lipschitz hH hL)=> t u.
  by rewrite -!(arc_length_factor_compose hfin); apply: hGL; [exists t | exists u].
move=> z w hz hw; rewrite -(curve_banach_extension_factor hH hz) -(curve_banach_extension_factor hH hw).
exact: hGL.
Qed.

(** Source for [curve_banach_extension_lipschitz_one]: Lip(H) <= 1,
    Federer 2.5.16, p. 110. *)
Lemma curve_banach_extension_lipschitz_one (H : R -> Y) :
  is_curve_banach_extension g H -> forall z w, mdist (H z) (H w) <= `|z - w|.
Proof.
move=> hH z w; rewrite -[`|z - w|]mul1r; apply: (curve_banach_lipschitz hH ler01)=> t u.
by rewrite mul1r; exact: (arc_length_distance_abs hfin).
Qed.

(** Source for [arc_length_cover]: every real number lies below a lower
    bound of im s, above an upper bound of im s, or between s(x-) and
    s(x+) for some x, Federer 2.5.16, p. 110. *)
Lemma arc_length_cover (z : R) :
  (forall t, z <= s t) \/ (forall t, s t <= z) \/ exists x, sl x <= z <= sr x.
Proof.
case: (pselect (forall t, z <= s t))=> [h|hlow]; first by left.
case: (pselect (forall t, s t <= z))=> [h|hup]; first by right; left.
right; right.
have [t1 ht1] : exists t, s t < z.
  by apply: contrapT=> hn; apply: hlow=> t; rewrite leNgt; apply/negP=> h; apply: hn; exists t.
have [t2 ht2] : exists t, z < s t.
  by apply: contrapT=> hn; apply: hup=> t; rewrite leNgt; apply/negP=> h; apply: hn; exists t.
pose T := [set t | s t < z].
have hT : T !=set0 by exists t1.
have hTub : ubound T t2.
  move=> t ht; rewrite leNgt; apply/negP=> h.
  by have := arc_length_monotone hfin (ltW h); rewrite leNgt (lt_trans ht ht2).
have hs : has_sup T by split=> //; exists t2.
exists (sup T); apply/andP; split.
- apply: ge_sup; first by exists (s (sup T - 1)), (sup T - 1)=> //=; lra.
  move=> _ [t /= htx <-].
  have hpos : 0 < sup T - t by rewrite subr_gt0.
  have [t' ht' htt'] := sup_adherent hpos hs.
  have htt'' : t < t' by lra.
  by apply: ltW; apply: le_lt_trans (arc_length_monotone hfin (ltW htt'')) ht'.
- rewrite /arc_length_right lerNr; apply: ge_sup.
    by exists (- s (sup T + 1)), (sup T + 1)=> //=; lra.
  move=> _ [t /= hxt <-]; rewrite lerN2 leNgt; apply/negP=> hlt.
  by have := sup_upper_bound hs hlt; rewrite leNgt hxt.
Qed.

(** Source for [curve_banach_extension_unique]: the printed formulas of
    Federer 2.5.16, p. 110, determine H. *)
Theorem curve_banach_extension_unique (H1 H2 : R -> Y) :
  is_curve_banach_extension g H1 -> is_curve_banach_extension g H2 -> H1 = H2.
Proof.
move=> h1 h2; apply/funext=> z.
case: (arc_length_cover z)=> [hlow|[hup|[x /andP[hlz hzr]]]].
- have hlb : has_lbound (range s) by exists z=> _ [t _ <-]; exact: hlow.
  have [y hy] := curve_limit_at_ninfty hfin hY hlb.
  by rewrite (curve_banach_ninfty h1 hy hlow) (curve_banach_ninfty h2 hy hlow).
- have hub : has_ubound (range s) by exists z=> _ [t _ <-]; exact: hup.
  have [y hy] := curve_limit_at_pinfty hfin hY hub.
  by rewrite (curve_banach_pinfty h1 hy hup) (curve_banach_pinfty h2 hy hup).
case: (leP z (s x))=> hzs.
  case: (eqVneq (sl x) (s x))=> [heq|hne].
    have -> : z = s x by apply/le_anti; rewrite hzs -heq hlz.
    by rewrite (curve_banach_compose h1) (curve_banach_compose h2).
  have hlt : sl x < s x by rewrite lt_neqAle hne (arc_length_left_le hfin x).
  pose l := (s x - z) / (s x - sl x).
  have hl : 0 <= l <= 1.
    rewrite /l; apply/andP; split; first by rewrite divr_ge0 // subr_ge0 // ltW.
    by rewrite ler_pdivrMr ?subr_gt0 // mul1r; lra.
  have hz : z = l * sl x + (1 - l) * s x by rewrite /l; field; rewrite subr_eq0 eq_sym.
  have [y hy] := curve_left_limit_exists hfin hY x.
  by rewrite hz (curve_banach_left h1 hy hl) (curve_banach_left h2 hy hl).
have hlt : s x < sr x := lt_le_trans hzs hzr.
pose l := (sr x - z) / (sr x - s x).
have hl : 0 <= l <= 1.
  rewrite /l; apply/andP; split; first by rewrite divr_ge0 // subr_ge0 // ltW.
  by rewrite ler_pdivrMr ?subr_gt0 // mul1r; lra.
have hz : z = l * s x + (1 - l) * sr x by rewrite /l; field; rewrite subr_eq0 eq_sym lt_eqF.
have [y hy] := curve_right_limit_exists hfin hY x.
by rewrite hz (curve_banach_right h1 hy hl) (curve_banach_right h2 hy hl).
Qed.

End CurveBanachExtension.
