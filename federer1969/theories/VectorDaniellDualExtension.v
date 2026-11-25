(** Federer (1969), 2.5.12, p. 104, third paragraph of the proof: whenever
    the map sending y into k_y(x) is Q linear and nu bounded on the
    countable dense rational subspace D, it has a unique extension k(x) in
    U* = E* cap {alpha : nu*(alpha) <= 1}. The extension is obtained here as
    the infimum alpha(z) = inf{a(y) + nu(z - y) : y in D}, which agrees with
    a on D and is Lipschitzian with constant 1; additivity and homogeneity
    over the rationals follow by approximation from D, and homogeneity over
    the reals by approximation of the scalar by rationals. Every member of
    E* is bounded, which gives the equivalence of nu*(alpha) <= 1 with the
    pointwise bound |<v, alpha>| <= nu(v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity
  VectorDaniellHypotheses VectorDaniellRationalSpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_small_zero]: a real number whose absolute value is
    below every positive number vanishes, the closing inference of the
    approximation arguments in Federer 2.5.12, p. 104. *)
Lemma real_small_zero (R : realType) (u : R) : (forall e, 0 < e -> `|u| < e) -> u = 0.
Proof.
move=> h; apply/eqP; rewrite -normr_eq0 eq_le normr_ge0 andbT.
by apply/ler_addgt0Pr=> e he; rewrite add0r; exact: ltW (h e he).
Qed.

Section DualSpace.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.

(** Source for [dual_unit_ball]: the set
    U* = E* cap {alpha : nu*(alpha) <= 1} of Federer 2.5.12, p. 104. *)
Definition dual_unit_ball : set (E -> R) := [set alpha | dual_space hN alpha /\ dual_norm N alpha <= 1].

(** Source for [dense_approximation]: every point of E is approximated
    in norm by points of a dense set, used throughout the proof of
    Federer 2.5.12, p. 104. *)
Lemma dense_approximation (D : set E) : dense (D : set (real_norm_metric_space hN)) ->
  forall (z : E) (e : R), 0 < e -> exists y, D y /\ N (z - y) < e.
Proof.
move=> hd z e he.
have hO : open (interior (ball (z : real_norm_metric_space hN) e)) := open_interior _.
have hne : interior (ball (z : real_norm_metric_space hN) e) !=set0.
  by exists z; exact: nbhsx_ballx.
have [y [hy1 hy2]] := hd _ hne hO.
exists y; split=> //.
by have := interior_subset hy1; rewrite ballEmdist /= real_norm_metric_distanceE.
Qed.

(** Source for [dual_space_linear]: the linearity of the members of E*,
    Federer 2.5.12(2), p. 102. *)
Lemma dual_space_linear (alpha : E -> R) : dual_space hN alpha ->
  forall c u v, alpha (c *: u + v) = c * alpha u + alpha v.
Proof. by move=> [h _] c u v; exact: h. Qed.

(** Source for [dual_space_zero]: a member of E* vanishes at zero,
    Federer 2.5.12(2), p. 102. *)
Lemma dual_space_zero (alpha : E -> R) : dual_space hN alpha -> alpha 0 = 0.
Proof.
move=> h; have := dual_space_linear h (-1) 0 0.
by rewrite scaler0 addr0 mulN1r addNr.
Qed.

(** Source for [dual_space_add]: additivity of the members of E*,
    Federer 2.5.12(2), p. 102. *)
Lemma dual_space_add (alpha : E -> R) (u v : E) : dual_space hN alpha ->
  alpha (u + v) = alpha u + alpha v.
Proof. by move=> h; have := dual_space_linear h 1 u v; rewrite scale1r mul1r. Qed.

(** Source for [dual_space_scale]: homogeneity of the members of E*,
    Federer 2.5.12(2), p. 102. *)
Lemma dual_space_scale (alpha : E -> R) (c : R) (u : E) : dual_space hN alpha ->
  alpha (c *: u) = c * alpha u.
Proof.
by move=> h; have := dual_space_linear h c u 0; rewrite addr0 (dual_space_zero h) addr0.
Qed.

(** Source for [dual_space_sub]: the members of E* preserve differences,
    Federer 2.5.12(2), p. 102. *)
Lemma dual_space_sub (alpha : E -> R) (u v : E) : dual_space hN alpha ->
  alpha (u - v) = alpha u - alpha v.
Proof.
move=> h; rewrite -scaleN1r (dual_space_add _ _ h) (dual_space_scale _ _ h).
by rewrite mulN1r.
Qed.

(** Source for [dual_space_bounded]: every nu continuous linear map is
    bounded, |<v, alpha>| <= C nu(v), the fact underlying the dual norm
    nu* of Federer 2.5.12(2), p. 102. *)
Lemma dual_space_bounded (alpha : E -> R) : dual_space hN alpha ->
  exists C, 0 <= C /\ forall v, `|alpha v| <= C * N v.
Proof.
move=> ha; have h0 := dual_space_zero ha.
have hW : nbhs (alpha 0 : real_line_metric R) (ball (alpha 0 : real_line_metric R) 1).
  exact: nbhsx_ballx.
have hpre := ha.2 (0 : real_norm_metric_space hN) _ hW.
have [d hd hball] := proj1 (metricType_numDomainType.nbhs_mdistP (0 : real_norm_metric_space hN) _) hpre.
exists (2 / d); split; first by rewrite divr_ge0 // ltW.
move=> v; have [->|hv] := eqVneq v 0.
  by rewrite h0 normr0 (real_seminorm_zero hN.1) mulr0.
have hNv : 0 < N v by rewrite (real_norm_positive hN.1 hN.2).
pose c := d / (2 * N v).
have hc : 0 < c by rewrite divr_gt0 // mulr_gt0.
have hw : mdist (0 : real_norm_metric_space hN) (c *: v : real_norm_metric_space hN) < d.
  rewrite real_norm_metric_distanceE sub0r (real_seminorm_negate hN.1) (real_seminorm_scale hN.1).
  have -> : `|c| * N v = d / 2 by rewrite gtr0_norm // /c; field; rewrite gt_eqF.
  have hd' : (0 : R) < d := hd.
  lra.
have h1 := hball _ hw.
have h2 : `|c * alpha v| < 1.
  move: h1; rewrite /= ballEmdist /= real_line_metric_distanceE h0 sub0r normrN.
  by rewrite (dual_space_scale _ _ ha).
rewrite normrM gtr0_norm // in h2.
have hci : c^-1 = 2 / d * N v by rewrite /c invf_div; field; rewrite gt_eqF.
rewrite -hci; apply: ltW; rewrite -(ltr_pM2l hc) mulfV ?gt_eqF //.
Qed.

(** Source for [dual_norm_le_one]: the pointwise bound |<v, alpha>| <= nu(v)
    implies nu*(alpha) <= 1, Federer 2.5.12(2), p. 102. *)
Lemma dual_norm_le_one (alpha : E -> R) : (forall v, `|alpha v| <= N v) -> dual_norm N alpha <= 1.
Proof.
move=> hb; rewrite /dual_norm.
have [hne|hemp] := pselect ([set alpha y | y in [set y | N y = 1]] !=set0).
  apply: ge_sup hne _ => _ [y hy <-]; apply: le_trans (ler_norm _) _; rewrite -hy; exact: hb.
have -> : [set alpha y | y in [set y | N y = 1]] = set0.
  by apply/seteqP; split=> [t ht|t []]; apply: hemp; exists t.
by rewrite sup0 ler01.
Qed.

(** Source for [dual_norm_bound]: nu*(alpha) <= 1 implies
    |<v, alpha>| <= nu(v) for alpha in E*, Federer 2.5.12(2), p. 102. *)
Lemma dual_norm_bound (alpha : E -> R) (v : E) : dual_space hN alpha -> dual_norm N alpha <= 1 ->
  `|alpha v| <= N v.
Proof.
move=> ha hn.
have [C [hC hCb]] := dual_space_bounded ha.
have [->|hv] := eqVneq v 0.
  by rewrite (dual_space_zero ha) normr0 (real_seminorm_zero hN.1).
have hNv : 0 < N v by rewrite (real_norm_positive hN.1 hN.2).
pose u := (N v)^-1 *: v.
have hNu : N u = 1 by rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have hNu' : N (- u) = 1 by rewrite (real_seminorm_negate hN.1).
have hsup : has_sup [set alpha y | y in [set y | N y = 1]].
  split; first by exists (alpha u); exists u.
  exists C => _ [y hy <-]; apply: le_trans (ler_norm _) _.
  by have := hCb y; rewrite hy mulr1.
have h1 : alpha u <= 1 := le_trans (sup_upper_bound hsup (imageP alpha hNu)) hn.
have h2 : alpha (- u) <= 1 := le_trans (sup_upper_bound hsup (imageP alpha hNu')) hn.
rewrite -scaleN1r (dual_space_scale _ _ ha) mulN1r in h2.
have hu : alpha u = (N v)^-1 * alpha v by rewrite (dual_space_scale _ _ ha).
have hau : `|alpha u| <= 1 by rewrite ler_norml; apply/andP; split; lra.
rewrite hu normrM gtr0_norm ?invr_gt0 // in hau.
have hi : 0 < (N v)^-1 by rewrite invr_gt0.
by rewrite -(ler_pM2l hi) mulVf ?gt_eqF.
Qed.

(** Source for [dual_unit_ball_bound]: membership in U* is equivalent to
    the pointwise bound |<v, alpha>| <= nu(v) for alpha in E*, Federer
    2.5.12, p. 104. *)
Lemma dual_unit_ball_bound (alpha : E -> R) :
  dual_unit_ball alpha <-> dual_space hN alpha /\ forall v, `|alpha v| <= N v.
Proof.
split=> [[ha hn]|[ha hb]]; first by split=> // v; exact: dual_norm_bound.
by split=> //; exact: dual_norm_le_one.
Qed.

(** Source for [zero_dual_unit_ball]: the zero functional belongs to U*,
    the value of k off the exceptional set in Federer 2.5.12, p. 104. *)
Lemma zero_dual_unit_ball : dual_unit_ball (fun _ => 0).
Proof.
apply/dual_unit_ball_bound; split; last by move=> v; rewrite normr0 (real_seminorm_nonnegative hN.1).
split; first by move=> c u v; rewrite mulr0 addr0.
exact: cst_continuous.
Qed.

(** Source for [dual_space_dense_eq]: two members of E* that agree on a
    dense set are equal, the uniqueness of the extension in Federer
    2.5.12, p. 104. *)
Lemma dual_space_dense_eq (D : set E) (alpha beta : E -> R) :
  dense (D : set (real_norm_metric_space hN)) -> dual_space hN alpha -> dual_space hN beta ->
  (forall y, D y -> alpha y = beta y) -> alpha = beta.
Proof.
move=> hd ha hb heq; apply/funext=> z; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: real_small_zero => e he.
have [Ca [hCa hCab]] := dual_space_bounded ha.
have [Cb [hCb hCbb]] := dual_space_bounded hb.
have hc : 0 < Ca + Cb + 1 by lra.
have [y [hy hzy]] := dense_approximation hd z (divr_gt0 he hc).
have h1 := hCab (z - y); have h2 := hCbb (z - y).
rewrite (dual_space_sub _ _ ha) (heq y hy) in h1; rewrite (dual_space_sub _ _ hb) in h2.
have h3 : (Ca + Cb + 1) * N (z - y) < e by rewrite mulrC -ltr_pdivlMr.
have hn := real_seminorm_nonnegative hN.1 (z - y).
have h4 : (Ca + Cb) * N (z - y) <= (Ca + Cb + 1) * N (z - y).
  have h01 : Ca + Cb <= Ca + Cb + 1 by rewrite lerDl.
  exact: (ler_wpM2r hn h01).
have h5 : `|alpha z - beta z| <= Ca * N (z - y) + Cb * N (z - y).
  have -> : alpha z - beta z = (alpha z - beta y) - (beta z - beta y) by ring.
  by apply: le_trans (ler_normB _ _) _; exact: lerD.
rewrite mulrDl in h4; lra.
Qed.

Section Extension.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable a : E -> R.
Hypothesis ha : forall (r s : rat) (y z : E), D y -> D z ->
  a (ratr r *: y + ratr s *: z) = ratr r * a y + ratr s * a z.
Hypothesis hb : forall y, D y -> `|a y| <= N y.

Let hDd : dense (D : set (real_norm_metric_space hN)) := hD.2.1.
Let hD0 : D 0 := hD.2.2.1.
Let hDc := hD.2.2.2.

(** Source for [rational_sub]: D is closed under differences and the
    Q linear map a preserves them, Federer 2.5.12, p. 104. *)
Lemma rational_sub (y z : E) : D y -> D z -> D (y - z) /\ a (y - z) = a y - a z.
Proof.
move=> hy hz; have e1 : ratr 1 *: y + ratr (-1) *: z = y - z.
  by rewrite rmorph1 rmorphN rmorph1 scale1r scaleN1r.
split; first by rewrite -e1; exact: hDc.
by rewrite -e1 ha // rmorph1 rmorphN rmorph1 mul1r mulN1r.
Qed.

(** Source for [rational_scale]: D is closed under rational multiples
    and a preserves them, Federer 2.5.12, p. 104. *)
Lemma rational_scale (q : rat) (y : E) : D y -> D (ratr q *: y) /\ a (ratr q *: y) = ratr q * a y.
Proof.
move=> hy; have e1 : ratr q *: y + ratr 0 *: y = ratr q *: y by rewrite rmorph0 scale0r addr0.
split; first by rewrite -e1; exact: hDc.
by rewrite -e1 ha // rmorph0 mul0r addr0.
Qed.

(** Source for [rational_add]: D is closed under sums and a preserves
    them, Federer 2.5.12, p. 104. *)
Lemma rational_add (y z : E) : D y -> D z -> D (y + z) /\ a (y + z) = a y + a z.
Proof.
move=> hy hz; have e1 : ratr 1 *: y + ratr 1 *: z = y + z by rewrite rmorph1 !scale1r.
split; first by rewrite -e1; exact: hDc.
by rewrite -e1 ha // rmorph1 !mul1r.
Qed.

(** Source for [rational_zero]: the map a vanishes at zero, since
    |a(0)| <= nu(0) = 0, Federer 2.5.12, p. 104. *)
Lemma rational_zero : a 0 = 0.
Proof. by have := hb hD0; rewrite (real_seminorm_zero hN.1) normr_le0 => /eqP. Qed.

(** Source for [rational_lipschitz]: a(y) - a(z) <= nu(y - z) on D,
    from the Q linearity and the nu bound, Federer 2.5.12, p. 104. *)
Lemma rational_lipschitz (y z : E) : D y -> D z -> a y - a z <= N (y - z).
Proof.
move=> hy hz; have [hyz he] := rational_sub hy hz.
by rewrite -he; exact: le_trans (ler_norm _) (hb hyz).
Qed.

(** Source for [dual_extension]: the extension of a from D to E, defined
    as alpha(z) = inf{a(y) + nu(z - y) : y in D}, supporting the unique
    extension k(x) in U* of Federer 2.5.12, p. 104. *)
Definition dual_extension (z : E) : R := inf [set a y + N (z - y) | y in D].

(** Source for [dual_extension_has_inf]: the set defining the extension
    is nonempty and bounded below by -nu(z), Federer 2.5.12, p. 104. *)
Lemma dual_extension_has_inf (z : E) : has_inf [set a y + N (z - y) | y in D].
Proof.
split; first by exists (a 0 + N (z - 0)); exists 0.
exists (- N z) => _ [y hy <-].
have h1 := hb hy.
have ht := real_seminorm_triangle hN.1 z (y - z).
rewrite addrC subrK (real_seminorm_subtract hN.1 y z) in ht.
rewrite ler_norml in h1; case/andP: h1 => h1 _.
lra.
Qed.

(** Source for [dual_extension_le]: alpha(z) <= a(y) + nu(z - y) for
    y in D, Federer 2.5.12, p. 104. *)
Lemma dual_extension_le (z y : E) : D y -> dual_extension z <= a y + N (z - y).
Proof.
by move=> hy; exact: (ge_inf (dual_extension_has_inf z).2 (imageP (fun y => a y + N (z - y)) hy)).
Qed.

(** Source for [dual_extension_ge]: a lower bound of the numbers
    a(y) + nu(z - y) is a lower bound of alpha(z), Federer 2.5.12,
    p. 104. *)
Lemma dual_extension_ge (z : E) (t : R) :
  (forall y, D y -> t <= a y + N (z - y)) -> t <= dual_extension z.
Proof. by move=> h; apply: lb_le_inf (dual_extension_has_inf z).1 _ => _ [y hy <-]; exact: h. Qed.

(** Source for [dual_extension_agree]: the extension agrees with a on D,
    Federer 2.5.12, p. 104. *)
Lemma dual_extension_agree (y : E) : D y -> dual_extension y = a y.
Proof.
move=> hy; apply/eqP; rewrite eq_le; apply/andP; split.
  by have := dual_extension_le y hy; rewrite subrr (real_seminorm_zero hN.1) addr0.
apply: dual_extension_ge => y' hy'.
have := rational_lipschitz hy hy'; lra.
Qed.

(** Source for [dual_extension_lipschitz]: the extension is Lipschitzian
    with constant 1, alpha(z) <= alpha(z') + nu(z - z'), Federer 2.5.12,
    p. 104. *)
Lemma dual_extension_lipschitz (z z' : E) : dual_extension z <= dual_extension z' + N (z - z').
Proof.
have h : dual_extension z - N (z - z') <= dual_extension z'.
  apply: dual_extension_ge => y hy.
  have h1 := dual_extension_le z hy.
  have ht := real_seminorm_triangle hN.1 (z - z') (z' - y).
  have e : z - z' + (z' - y) = z - y by rewrite addrA subrK.
  rewrite e in ht; lra.
lra.
Qed.

(** Source for [dual_extension_lipschitz_abs]: the estimate
    |alpha(z) - alpha(z')| <= nu(z - z'), Federer 2.5.12, p. 104. *)
Lemma dual_extension_lipschitz_abs (z z' : E) :
  `|dual_extension z - dual_extension z'| <= N (z - z').
Proof.
have h1 := dual_extension_lipschitz z z'; have h2 := dual_extension_lipschitz z' z.
rewrite (real_seminorm_subtract hN.1 z' z) in h2.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [dual_extension_zero]: the extension vanishes at zero,
    Federer 2.5.12, p. 104. *)
Lemma dual_extension_zero : dual_extension 0 = 0.
Proof. by rewrite dual_extension_agree // rational_zero. Qed.

(** Source for [dual_extension_bound]: the estimate |alpha(z)| <= nu(z),
    Federer 2.5.12, p. 104. *)
Lemma dual_extension_bound (z : E) : `|dual_extension z| <= N z.
Proof. by have := dual_extension_lipschitz_abs z 0; rewrite dual_extension_zero !subr0. Qed.

(** Source for [dual_extension_add]: additivity of the extension, by
    approximation from D, Federer 2.5.12, p. 104. *)
Lemma dual_extension_add (z1 z2 : E) :
  dual_extension (z1 + z2) = dual_extension z1 + dual_extension z2.
Proof.
apply/eqP; rewrite -subr_eq0; apply/eqP; apply: real_small_zero => e he.
have he4 : 0 < e / 4 by lra.
have [y1 [hy1 h1]] := dense_approximation hDd z1 he4.
have [y2 [hy2 h2]] := dense_approximation hDd z2 he4.
have [hy12 ha12] := rational_add hy1 hy2.
have hext : dual_extension (y1 + y2) = dual_extension y1 + dual_extension y2.
  by rewrite !dual_extension_agree.
have l1 := dual_extension_lipschitz_abs (z1 + z2) (y1 + y2).
have l2 := dual_extension_lipschitz_abs z1 y1.
have l3 := dual_extension_lipschitz_abs z2 y2.
have e12 : z1 + z2 - (y1 + y2) = (z1 - y1) + (z2 - y2) by rewrite opprD addrACA.
have ht := real_seminorm_triangle hN.1 (z1 - y1) (z2 - y2).
rewrite -e12 in ht.
rewrite ler_norml in l1; rewrite ler_norml in l2; rewrite ler_norml in l3.
case/andP: l1 => l1a l1b; case/andP: l2 => l2a l2b; case/andP: l3 => l3a l3b.
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [dual_extension_rational_scale]: homogeneity of the
    extension for rational scalars, by approximation from D, Federer
    2.5.12, p. 104. *)
Lemma dual_extension_rational_scale (q : rat) (z : E) :
  dual_extension (ratr q *: z) = ratr q * dual_extension z.
Proof.
apply/eqP; rewrite -subr_eq0; apply/eqP; apply: real_small_zero => e he.
pose c := `|ratr q : R|.
have hc : 0 <= c := normr_ge0 _.
have hc1 : 0 < 2 * c + 1 by lra.
have hd : 0 < e / (2 * c + 1) by rewrite divr_gt0.
have [y [hy hzy]] := dense_approximation hDd z hd.
have [hqy haq] := rational_scale q hy.
have hext : dual_extension (ratr q *: y) = ratr q * dual_extension y.
  by rewrite !dual_extension_agree.
have l1 := dual_extension_lipschitz_abs (ratr q *: z) (ratr q *: y).
rewrite -scalerBr (real_seminorm_scale hN.1) -/c in l1.
have l2 : `|ratr q * dual_extension z - ratr q * dual_extension y| <= c * N (z - y).
  rewrite -mulrBr normrM.
  have hlz := dual_extension_lipschitz_abs z y.
  exact (ler_wpM2l hc hlz).
have ht : 0 <= N (z - y) := real_seminorm_nonnegative hN.1 _.
have h3 : (2 * c + 1) * N (z - y) < e by rewrite mulrC -ltr_pdivlMr.
have h4 : 2 * (c * N (z - y)) <= (2 * c + 1) * N (z - y).
  have -> : (2 * c + 1) * N (z - y) = 2 * (c * N (z - y)) + N (z - y) by ring.
  lra.
rewrite ler_norml in l1; rewrite ler_norml in l2.
case/andP: l1 => l1a l1b; case/andP: l2 => l2a l2b.
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [dual_extension_scale]: homogeneity of the extension for
    real scalars, by approximation of the scalar by rationals, Federer
    2.5.12, p. 104. *)
Lemma dual_extension_scale (c : R) (z : E) : dual_extension (c *: z) = c * dual_extension z.
Proof.
apply/eqP; rewrite -subr_eq0; apply/eqP; apply: real_small_zero => e he.
pose n := N z.
have hn : 0 <= n := real_seminorm_nonnegative hN.1 z.
have hn1 : 0 < 2 * n + 1 by lra.
pose d := e / (2 * n + 1).
have hd : 0 < d by rewrite divr_gt0.
have hcd : c - d < c + d by lra.
have [q hq] := rat_in_itvoo hcd.
rewrite in_itv /= in hq; case/andP: hq => hq1 hq2.
pose s := `|c - ratr q|.
have hs : 0 <= s := normr_ge0 _.
have hsd : s < d by rewrite /s ltr_norml; apply/andP; split; lra.
have l1 := dual_extension_lipschitz_abs (c *: z) (ratr q *: z).
rewrite -scalerBl (real_seminorm_scale hN.1) -/s -/n in l1.
have hrat := dual_extension_rational_scale q z.
have l2 : `|ratr q * dual_extension z - c * dual_extension z| <= s * n.
  rewrite -mulrBl normrM distrC.
  have hbz : `|dual_extension z| <= n := dual_extension_bound z.
  exact (ler_wpM2l hs hbz).
have h3 : s * (2 * n + 1) < d * (2 * n + 1) by rewrite ltr_pM2r.
have h3' : d * (2 * n + 1) = e by rewrite /d; field; rewrite gt_eqF.
have h4 : s * n + s * n <= s * (2 * n + 1).
  have -> : s * (2 * n + 1) = s * n + s * n + s by ring.
  lra.
rewrite ler_norml in l1; rewrite ler_norml in l2.
case/andP: l1 => l1a l1b; case/andP: l2 => l2a l2b.
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [dual_extension_linear]: the extension is linear,
    Federer 2.5.12, p. 104. *)
Lemma dual_extension_linear : scalar dual_extension.
Proof. by move=> c u v; rewrite dual_extension_add dual_extension_scale. Qed.

(** Source for [dual_extension_continuous]: the extension is nu
    continuous, being Lipschitzian, Federer 2.5.12, p. 104. *)
Lemma dual_extension_continuous :
  continuous (dual_extension : real_norm_metric_space hN -> real_line_metric R).
Proof.
apply: (@metric_fixed_lipschitz_continuous R [the metricType R of real_norm_metric_space hN]
  [the metricType R of real_line_metric R] (fun y => dual_extension y) 1 ler01).
move=> x y; change (`|dual_extension x - dual_extension y| <= 1 * N (x - y)).
by rewrite mul1r; exact: dual_extension_lipschitz_abs.
Qed.

(** Source for [dual_extension_dual]: the extension belongs to E*,
    Federer 2.5.12, p. 104. *)
Theorem dual_extension_dual : dual_space hN dual_extension.
Proof. by split; [exact: dual_extension_linear | exact: dual_extension_continuous]. Qed.

(** Source for [dual_extension_unit_ball]: the extension belongs to U*,
    Federer 2.5.12, p. 104. *)
Theorem dual_extension_unit_ball : dual_unit_ball dual_extension.
Proof.
by apply/dual_unit_ball_bound; split; [exact: dual_extension_dual | exact: dual_extension_bound].
Qed.

End Extension.

(** Source for [is_dual_extension]: alpha in E* extends the map a given
    on D, Federer 2.5.12, p. 104. *)
Definition is_dual_extension (D : set E) (a alpha : E -> R) : Prop :=
  dual_space hN alpha /\ forall y, D y -> alpha y = a y.

(** Source for [dual_extension_exists]: a Q linear and nu bounded map on
    the countable dense rational subspace D has an extension in U*,
    Federer 2.5.12, p. 104. *)
Theorem dual_extension_exists (D : set E) (a : E -> R) : is_rational_dense_subspace hN D ->
  (forall (r s : rat) (y z : E), D y -> D z -> a (ratr r *: y + ratr s *: z) = ratr r * a y + ratr s * a z) ->
  (forall y, D y -> `|a y| <= N y) ->
  exists alpha, is_dual_extension D a alpha /\ dual_unit_ball alpha.
Proof.
move=> hD ha hb; exists (dual_extension D a); split; last exact: dual_extension_unit_ball.
by split; [exact: dual_extension_dual | move=> y hy; exact: dual_extension_agree].
Qed.

(** Source for [dual_extension_unique]: the extension is unique, Federer
    2.5.12, p. 104. *)
Theorem dual_extension_unique (D : set E) (a alpha beta : E -> R) :
  dense (D : set (real_norm_metric_space hN)) ->
  is_dual_extension D a alpha -> is_dual_extension D a beta -> alpha = beta.
Proof.
move=> hd [ha hea] [hb heb]; apply: dual_space_dense_eq hd ha hb _ => y hy.
by rewrite hea // heb.
Qed.

End DualSpace.
