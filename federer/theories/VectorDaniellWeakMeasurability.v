(** Federer (1969), 2.5.12, pp. 104–105, fourth and fifth paragraphs of the
    proof: the sets U* cap {alpha : a < <y, alpha> < b} with y in D and
    rational a, b form a countable family generating the weak topology on
    U*; since each <y, k> = k_y is phi measurable, so is k. Moreover nu* o k
    is phi measurable, because nu*[k(x)] = sup{<y, k(x)> : y in D, nu(y) <
    1}. The generating property is proved through the finite coordinate
    boxes of the product topology on the real valued functions on E, and the
    measurability of k through a relative form of the countable base
    criterion. The family is indexed by finite sequences of triples formed
    from an enumeration of D and two rationals. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP
  PartialFunctionBasic PartialFunctionPreimages FunctionLatticeUP MeasureUP MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableAlmostModification
  MeasureCountableClosure RealIntegralFunctionalUP FunctionLatticeRegularityUP
  CountablyMeasurableUP SummableRealFunctionUP TotalScalarLpUP TotalScalarMeasurability
  RealLatticeDensityUP MeasureStepIntegralIdentification PartialFunctionSupremumUP
  MeasurableCountableSupremum VectorDaniellHypotheses VectorDaniellRationalSpan
  VectorDaniellDualExtension VectorDaniellDualDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_relative_countable_base]: a function with
    values in a subset S is measurable when the inverse images of a
    countable family B are measurable and every open set contains,
    around each of its points in S, a member of B up to points outside
    S; the criterion used for the countable family generating the weak
    topology on U* in Federer 2.5.12, p. 105. *)
Lemma measurable_relative_countable_base (R : realType) (X : choiceType) (Y : topologicalType)
    (J : countType) (mu : set X -> \bar R) (hm : is_measure mu) (S : set Y) (B : J -> set Y)
    (f : X -> Y) :
  (forall x, S (f x)) ->
  (forall V, open V -> forall y, S y -> V y -> exists j, B j y /\ B j `&` S `<=` V) ->
  (forall j, measure_measurable mu (f @^-1` B j)) ->
  is_measure_measurable_function mu (partial_function_total f).
Proof.
move=> hS hB hf; constructor.
  by rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
move=> V hV; rewrite partial_function_total_preimage.
have -> : f @^-1` V = \bigcup_(j in [set j | B j `&` S `<=` V]) (f @^-1` B j).
  apply/seteqP; split=> x hx.
    by have [j [hj hjV]] := hB V hV (f x) (hS x) hx; exists j.
  by have [j hj hxj] := hx; exact: hj (f x) (conj hxj (hS x)).
apply: (measure_measurable_countable_union hm); first exact: countableP.
by move=> j _; exact: hf.
Qed.

(** Source for [countable_enumeration]: a countable set containing a
    given point is the range of a sequence, used to index the countable
    family of Federer 2.5.12, p. 105. *)
Lemma countable_enumeration (E : choiceType) (D : set E) (y0 : E) : countable D -> D y0 ->
  exists e : nat -> E, (forall n, D (e n)) /\ (forall y, D y -> exists n, e n = y).
Proof.
move=> /countable_injP [f hf] hy0.
pose e n := xget y0 [set y | D y /\ f y = n].
exists e; split.
  by move=> n; rewrite /e; case: xgetP => [y _ [hy _]|_]; [exact: hy | exact: hy0].
move=> y hy; exists (f y); rewrite /e.
have hex : exists u, D u /\ f u = f y by exists y.
have [hu hfu] := xgetPex y0 hex.
exact: hf (mem_set hu) (mem_set hy) hfu.
Qed.

(** Source for [real_interval_preimage_measurable]: the set
    {x : a < g(x) < b} is measurable for a measurable real function g,
    the open inverse image clause of 2.3.2, p. 73, used in Federer
    2.5.12, p. 105. *)
Lemma real_interval_preimage_measurable (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (g : X -> R) (a b : R) :
  is_measure_measurable_function mu (partial_function_total (g : X -> real_line_metric R)) ->
  measure_measurable mu [set x | a < g x < b].
Proof.
move=> hg.
have hU : open [set t : real_line_metric R | a < t < b].
  have -> : [set t : real_line_metric R | a < t < b] = [set t : real_line_metric R | a < t] `&` [set t | t < b].
    by apply/seteqP; split=> t /=; [move/andP|move=> [h1 h2]; apply/andP].
  exact: openI (@open_gt R a) (@open_lt R b).
have := measurable_function_open_preimage hg hU.
by rewrite partial_function_total_preimage.
Qed.

Section ProductBox.
Variable R : realType.
Variable E : lmodType R.

(** Source for [weak_box]: the set of real functions on E within e of b
    at each point of a finite sequence s, a basic neighbourhood of the
    weak topology in Federer 2.5.12, p. 103. *)
Definition weak_box (b : weak_function_space E) (s : seq E) (e : R) : set (weak_function_space E) :=
  [set c | forall z, z \in s -> `|(c : E -> R) z - (b : E -> R) z| < e].

(** Source for [weak_function_nbhs_box]: every neighbourhood of b in the
    topology of pointwise convergence contains a box, the description of
    the weak topology by the sets {alpha : a < <z, alpha> < b} in Federer
    2.5.12, p. 103. *)
Lemma weak_function_nbhs_box (b : weak_function_space E) (A : set (weak_function_space E)) :
  nbhs b A -> exists s : seq E, exists e : R, 0 < e /\ weak_box b s e `<=` A.
Proof.
move=> hA.
pose G := filter_from [set p : seq E * R | 0 < p.2] (fun p => weak_box b p.1 p.2).
have hG : Filter G.
  apply: filter_from_filter; first by exists ([::], 1); exact: ltr01.
  move=> [s1 e1] [s2 e2] /= h1 h2; exists (s1 ++ s2, Order.min e1 e2); first by rewrite /= lt_min h1 h2.
  move=> c /= hc; split=> z hz.
  - by apply: lt_le_trans (hc z _) _; [rewrite mem_cat hz | rewrite ge_min lexx].
  - by apply: lt_le_trans (hc z _) _; [rewrite mem_cat hz orbT | rewrite ge_min lexx orbT].
have hc : G --> (b : weak_function_space E).
  apply/cvg_sup=> i V; rewrite (@nbhsE (initial_topology (fun c : weak_function_space E => c i))).
  move=> [W [[O hO <-] hbi] hWV].
  have hn : nbhs ((b : E -> R) i : real_line_metric R) O by rewrite openE in hO; exact: hO _ hbi.
  have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP ((b : E -> R) i : real_line_metric R) _) hn.
  exists ([:: i], e) => // c hci; apply: hWV; apply: hball.
  by rewrite /= real_line_metric_distanceE distrC; exact: hci i (mem_head _ _).
have [[s e] /= he hsub] := hc A hA.
by exists s, e.
Qed.

End ProductBox.

Section WeakMeasurability.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.

Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi Lp lam.
Hypothesis hreg : is_function_lattice_regular Lp phi.
Hypothesis hX : measure_countably_measurable phi setT.

Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_component_density_family N L T phi kk.

Local Notation k := (vector_density N D kk).
Local Notation kp := (vector_density_point hD kk).

(** Source for [vector_density_component_measurable]: <y, k> is phi
    measurable for y in D, being almost equal to k_y, Federer 2.5.12,
    p. 105. *)
Lemma vector_density_component_measurable (y : E) : D y ->
  is_measure_measurable_function phi (partial_function_total (fun x => (k x y : real_line_metric R))).
Proof.
move=> hy.
have hm2 := total_scalar_real_measurable hphi (hkk y).1.1.
apply: (measurable_function_almost_equal hphi hm2).
rewrite /measure_almost_equal partial_function_total_agreement.
apply: (measure_almost_everywhere_mono hphi _
  (vector_density_component_ae hL hQ hM hT hphi hrep hreg hX hD hkk hy)).
by move=> x /= ->.
Qed.

(** Source for [dense_unit_values_zero]: <0, alpha> belongs to the set
    {<y, alpha> : y in D, nu(y) < 1}, Federer 2.5.12, p. 105. *)
Lemma dense_unit_values_zero (alpha : E -> R) :
  [set alpha y | y in D `&` [set y | N y < 1]] (alpha 0).
Proof.
exists 0 => //; split; first exact: hD.2.2.1.
by rewrite /= (real_seminorm_zero hN.1) ltr01.
Qed.

(** Source for [dense_unit_values_has_sup]: for alpha in U* the set
    {<y, alpha> : y in D, nu(y) < 1} is nonempty and bounded above by 1,
    Federer 2.5.12, p. 105. *)
Lemma dense_unit_values_has_sup (alpha : E -> R) : dual_unit_ball hN alpha ->
  has_sup [set alpha y | y in D `&` [set y | N y < 1]].
Proof.
move=> /dual_unit_ball_bound [_ hab]; split; first by exists (alpha 0); exact: dense_unit_values_zero.
exists 1 => _ [y [_ hy] <-]; apply: le_trans (ler_norm _) _.
by apply: le_trans (hab y) _; exact: ltW.
Qed.

(** Source for [dual_norm_dense_sup]: the formula
    nu*(alpha) = sup{<y, alpha> : y in D, nu(y) < 1} for alpha in U*,
    Federer 2.5.12, p. 105. *)
Lemma dual_norm_dense_sup (alpha : E -> R) : dual_unit_ball hN alpha ->
  dual_norm N alpha = sup [set alpha y | y in D `&` [set y | N y < 1]].
Proof.
move=> ha; have /dual_unit_ball_bound [had hab] := ha.
have ha0 : alpha 0 = 0 := dual_space_zero had.
have hS2 := dense_unit_values_has_sup ha.
have hs20 : 0 <= sup [set alpha y | y in D `&` [set y | N y < 1]].
  by have := sup_upper_bound hS2 (dense_unit_values_zero alpha); rewrite ha0.
rewrite /dual_norm.
have [hne|hemp] := pselect ([set alpha y | y in [set y | N y = 1]] !=set0); last first.
  have -> : [set alpha y | y in [set y | N y = 1]] = set0.
    by apply/seteqP; split=> [t ht|t []]; apply: hemp; exists t.
  rewrite sup0; apply/eqP; rewrite eq_le hs20 andTb.
  apply: ge_sup hS2.1 _ => _ [y [hy hNy] <-].
  have [->|hy0] := eqVneq y 0; first by rewrite ha0.
  have hNp : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
  exfalso; apply: hemp; exists (alpha ((N y)^-1 *: y)); exists ((N y)^-1 *: y) => //.
  by rewrite /= (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have hS1 : has_sup [set alpha y | y in [set y | N y = 1]].
  split=> //; exists 1 => _ [y hy <-]; apply: le_trans (ler_norm _) _; rewrite -hy; exact: hab.
have hs10 : 0 <= sup [set alpha y | y in [set y | N y = 1]].
  have [t [u hu _]] := hne.
  have h1 := sup_upper_bound hS1 (imageP alpha hu).
  have hu' : N (- u) = 1 by rewrite (real_seminorm_negate hN.1).
  have h2 := sup_upper_bound hS1 (imageP alpha hu').
  rewrite -scaleN1r (dual_space_scale _ _ had) mulN1r in h2.
  lra.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_sup hne _ => _ [u hu <-].
  apply/ler_addgt0Pr => eps heps.
  pose d := Order.min (eps / 3) (1 / 8).
  have hd : 0 < d by rewrite lt_min; apply/andP; split; lra.
  have hd1 : d <= eps / 3 by rewrite ge_min lexx.
  have hd2 : d <= 1 / 8 by rewrite ge_min lexx orbT.
  have [y [hy hy']] := dense_approximation hD.2.1 ((1 - 2 * d) *: u) hd.
  have hNy : N y < 1.
    have ht := real_seminorm_triangle hN.1 ((1 - 2 * d) *: u) (y - (1 - 2 * d) *: u).
    rewrite addrC subrK (real_seminorm_scale hN.1) hu mulr1 in ht.
    rewrite (real_seminorm_subtract hN.1) in ht.
    have h12 : 0 <= 1 - 2 * d by lra.
    rewrite ger0_norm // in ht; lra.
  have hyS : [set alpha y | y in D `&` [set y | N y < 1]] (alpha y) by exists y.
  have h1 := sup_upper_bound hS2 hyS.
  have h2 := hab ((1 - 2 * d) *: u - y).
  rewrite (dual_space_sub _ _ had) (dual_space_scale _ _ had) in h2.
  rewrite ler_norml in h2; case/andP: h2 => h2a h2b.
  have h3 := hab u; rewrite hu ler_norml in h3; case/andP: h3 => h3a h3b.
  have h2d : 0 <= 2 * d by lra.
  have h5 : 2 * d * alpha u <= 2 * d * 1 := ler_wpM2l h2d h3b.
  lra.
apply: ge_sup hS2.1 _ => _ [y [hy hNy] <-].
have [->|hy0] := eqVneq y 0; first by rewrite ha0.
have hNp : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
pose u := (N y)^-1 *: y.
have hu : N u = 1 by rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have h1 := sup_upper_bound hS1 (imageP alpha hu).
have hy' : y = N y *: u by rewrite /u scalerA mulfV ?gt_eqF // scale1r.
rewrite hy' (dual_space_scale _ _ had).
have h2 : N y * alpha u <= N y * sup [set alpha y | y in [set y | N y = 1]] := ler_wpM2l (ltW hNp) h1.
have h3 : N y * sup [set alpha y | y in [set y | N y = 1]] <= 1 * sup [set alpha y | y in [set y | N y = 1]].
  exact: (ler_wpM2r hs10 (ltW hNy)).
lra.
Qed.

(** Source for [vector_density_norm_measurable]: nu* o k is phi
    measurable, by the formula nu*[k(x)] = sup{<y, k(x)> : y in D,
    nu(y) < 1} and 2.3.2, Federer 2.5.12, p. 105. *)
Theorem vector_density_norm_measurable :
  is_measure_measurable_function phi (real_total_integrand (fun x => dual_norm N (k x))).
Proof.
apply: (measurable_countable_supremum hphi (D := D `&` [set y | N y < 1])
  (f := fun y => real_total_integrand (fun x => k x y))).
- exact: (sub_countable (subset_card_le (@subIsetl _ D _)) hD.1).
- move=> y [hy _].
  exact (measurable_partial_real_embedding hphi (vector_density_component_measurable hy)).
- constructor.
  + apply/seteqP; split=> x _.
      by move=> y _; exists (k x y)%:E; apply/real_total_integrand_graph.
    by exists (dual_norm N (k x))%:E; apply/real_total_integrand_graph.
  + move=> x t ht z [y [[hy hNy] hz]].
    move/real_total_integrand_graph: ht => <-; move/real_total_integrand_graph: hz => <-.
    have hk := vector_density_unit_ball hD kk x.
    rewrite lee_fin (dual_norm_dense_sup hk).
    have hyS : [set k x y | y in D `&` [set y | N y < 1]] (k x y) by exists y.
    exact: (sup_upper_bound (dense_unit_values_has_sup hk) hyS).
  + move=> x t ht b hb; move/real_total_integrand_graph: ht => <-.
    have hk := vector_density_unit_ball hD kk x.
    have h0 : ((k x 0)%:E <= b)%E.
      apply: hb; exists 0; split.
        by split; [exact: hD.2.2.1 | rewrite /= (real_seminorm_zero hN.1) ltr01].
      by apply/real_total_integrand_graph.
    case: b hb h0 => [r| |] hb h0.
    * rewrite lee_fin (dual_norm_dense_sup hk).
      apply: ge_sup (dense_unit_values_has_sup hk).1 _ => _ [y hy <-].
      rewrite -lee_fin; apply: hb; exists y; split=> //.
      by apply/real_total_integrand_graph.
    * exact: leey.
    * by have := lt_le_trans (ltNyr (k x 0)) h0; rewrite ltxx.
Qed.

Variable e : nat -> E.
Hypothesis he1 : forall n, D (e n).
Hypothesis he2 : forall y, D y -> exists n, e n = y.

(** Source for [weak_basic]: the finite intersections of the sets
    {alpha : a < <y, alpha> < b} with y in D and rational a, b, the
    countable family of Federer 2.5.12, p. 105, indexed through the
    enumeration e of D. *)
Definition weak_basic (s : seq (nat * rat * rat)) : set (weak_dual_space hN) :=
  [set beta | forall p, p \in s -> ratr p.1.2 < (val beta : E -> R) (e p.1.1) < ratr p.2].

(** Source for [weak_basic_preimage_measurable]: the inverse images
    under k of the members of the countable family are phi measurable,
    Federer 2.5.12, p. 105. *)
Lemma weak_basic_preimage_measurable (s : seq (nat * rat * rat)) :
  measure_measurable phi (kp @^-1` weak_basic s).
Proof.
have -> : kp @^-1` weak_basic s
    = \bigcap_(p in [set p | p \in s]) [set x | ratr p.1.2 < k x (e p.1.1) < ratr p.2].
  by apply/seteqP; split=> x hx p hp; exact: hx p hp.
apply: (measure_measurable_countable_intersection hphi); first exact: countableP.
move=> p _; apply: real_interval_preimage_measurable.
exact: vector_density_component_measurable (he1 _).
Qed.

(** Source for [weak_approximation_point]: for z in E and eps > 0 there
    are y = e(n) in D with nu(z - y) < eps/4 and rationals a < <y, alpha>
    < b with b - a < eps/2, Federer 2.5.12, p. 105. *)
Lemma weak_approximation_point (alpha : weak_dual_space hN) (z : E) (eps : R) : 0 < eps ->
  exists p : nat * rat * rat, N (z - e p.1.1) < eps / 4 /\
    ratr p.1.2 < (val alpha : E -> R) (e p.1.1) < ratr p.2 /\ ratr p.2 - ratr p.1.2 < eps / 2.
Proof.
move=> he.
have he4 : 0 < eps / 4 by lra.
have [y [hy hzy]] := dense_approximation hD.2.1 z he4.
have [n hn] := he2 hy.
have h1 : (val alpha : E -> R) y - eps / 4 < (val alpha : E -> R) y by lra.
have h2 : (val alpha : E -> R) y < (val alpha : E -> R) y + eps / 4 by lra.
have [a ha] := rat_in_itvoo h1; have [b hb] := rat_in_itvoo h2.
have /andP [ha1 ha2] : (val alpha : E -> R) y - eps / 4 < ratr a < (val alpha : E -> R) y := ha.
have /andP [hb1 hb2] : (val alpha : E -> R) y < ratr b < (val alpha : E -> R) y + eps / 4 := hb.
exists (n, a, b); rewrite /= hn; split=> //; split; first by rewrite ha2 hb1.
lra.
Qed.

(** Source for [weak_basic_refines]: every weakly open set contains,
    around each of its points in U*, a member of the countable family up
    to points outside U*, so that the family generates the weak topology
    on U*, Federer 2.5.12, p. 105. *)
Lemma weak_basic_refines (V : set (weak_dual_space hN)) (alpha : weak_dual_space hN) :
  open V -> V alpha -> dual_unit_ball hN (val alpha) ->
  exists s, weak_basic s alpha /\
    weak_basic s `&` [set beta : weak_dual_space hN | dual_unit_ball hN (val beta)] `<=` V.
Proof.
move=> [A hA hVA] hVa ha.
rewrite -hVA in hVa.
have hn : nbhs (val alpha : weak_function_space E) A by rewrite openE in hA; exact: hA _ hVa.
have [zs [eps [heps hbox]]] := weak_function_nbhs_box hn.
pose pick z := sval (cid (weak_approximation_point alpha z heps)).
have hpick : forall z, N (z - e (pick z).1.1) < eps / 4 /\
    ratr (pick z).1.2 < (val alpha : E -> R) (e (pick z).1.1) < ratr (pick z).2 /\
    ratr (pick z).2 - ratr (pick z).1.2 < eps / 2.
  by move=> z; exact: svalP (cid (weak_approximation_point alpha z heps)).
exists (map pick zs); split.
  by move=> p /mapP [z hz ->]; exact: (hpick z).2.1.
move=> beta [hbs hb]; rewrite -hVA; apply: hbox => z hz.
suff hgoal : `|(val beta : E -> R) z - (val alpha : E -> R) z| < eps by exact: hgoal.
have hp : pick z \in map pick zs by exact: map_f.
have [hzn [/andP [ha1 ha2] hab]] := hpick z.
have /andP [hb1 hb2] := hbs _ hp.
have /dual_unit_ball_bound [hbd hbb] := hb.
have /dual_unit_ball_bound [had hab'] := ha.
have hb3 := hbb (z - e (pick z).1.1); have ha3 := hab' (z - e (pick z).1.1).
rewrite (dual_space_sub _ _ hbd) in hb3; rewrite (dual_space_sub _ _ had) in ha3.
rewrite ler_norml in hb3; rewrite ler_norml in ha3.
case/andP: hb3 => hb3a hb3b; case/andP: ha3 => ha3a ha3b.
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [vector_density_weak_measurable_enumerated]: k is phi
    measurable with values in the weakly topologized space E*, Federer
    2.5.12, p. 105, for a given enumeration of D. *)
Theorem vector_density_weak_measurable_enumerated :
  is_measure_measurable_function phi (partial_function_total kp).
Proof.
apply: (measurable_relative_countable_base hphi
  (S := [set beta : weak_dual_space hN | dual_unit_ball hN (val beta)]) (B := weak_basic)).
- by move=> x; exact: (vector_density_unit_ball hD kk x).
- by move=> V hV beta hb hVb; exact: weak_basic_refines hV hVb hb.
- exact: weak_basic_preimage_measurable.
Qed.

End WeakMeasurability.

Section WeakMeasurabilityConclusion.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi (positive_function_lattice L) (variation_integral N Q T).
Hypothesis hreg : is_function_lattice_regular (positive_function_lattice L) phi.
Hypothesis hX : measure_countably_measurable phi setT.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_component_density_family N L T phi kk.

(** Source for [vector_density_weak_measurable]: k is phi measurable
    with values in the weakly topologized space E*, Federer 2.5.12,
    p. 105. *)
Theorem vector_density_weak_measurable :
  is_measure_measurable_function phi (partial_function_total (vector_density_point hD kk)).
Proof.
have [e [he1 he2]] := countable_enumeration hD.1 hD.2.2.1.
exact (vector_density_weak_measurable_enumerated hL hQ hM hT hphi hrep hreg hX hD hkk he1 he2).
Qed.

End WeakMeasurabilityConclusion.
