(** Federer (1969), 2.5.18(3), p. 112: if phi measures X, phi(X) < oo, u is
    an R valued phi measurable function and g(t) = phi{x : u(x) < t} for t
    in R, then g is nondecreasing and int (f o u) dphi = int_a^b f dg
    whenever f in K(R) and spt f subset {t : a <= t <= b}; one calls g the
    phi distribution function of u. Federer infers the identity from the
    agreement of u_#(phi) with the measure psi^+ of 2.5.17 on Borel sets and
    from 2.4.18. Here the identity is obtained directly from the definitions
    of 2.5.17: every Riemann-Stieltjes sum of f with respect to g is the phi
    integral of a simple function which differs from f o u by at most the
    oscillation of f on cells of the sequence, and the integral of 2.5.17 is
    the limit of these sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureSplit MeasureFiniteClosure MeasurableFunctionUP PartialFunctionUP
  PartialFunctionBasic PartialFunctionPreimages MeasureStepIntegralIdentification
  MeasurableTotalBasic BorelFunctionBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralComparison CharacteristicFunctionUP MeasureCharacteristicIntegral
  SummableRealFunctionUP SummableRealArithmetic RealTotalCharacteristicBounds
  LatticeL1ApproximationLaws FunctionLatticeUP CompactSupportFunctionUP CompactMaximum
  SegmentUniformContinuity CurveVariationUP CurveArcLength StieltjesSums StieltjesIntegral
  StieltjesMonotone StieltjesDaniellIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SupportFacts.
Variable R : realType.

(** Source for [support_segment_vanish]: a function whose support lies
    in {t : a <= t <= b} vanishes outside that segment, the meaning of
    the hypothesis spt f subset {t : a <= t <= b} of Federer 2.5.18(3),
    p. 112. *)
Lemma support_segment_vanish (f : R -> R) (a b : R) :
  real_function_support f `<=` `[a, b] -> forall x, x < a \/ b < x -> f x = 0.
Proof.
move=> hs x hx; have [hz|hne] := eqVneq (f x) 0; first by [].
have hne' : f x <> 0 by apply/eqP.
have /andP[h1 h2] : a <= x <= b by have := hs x (subset_closure hne'); rewrite set_itvcc.
by case: hx=> h; [move: (lt_le_trans h h1)|move: (le_lt_trans h2 h)]; rewrite ltxx.
Qed.

(** Source for [vanish_right_limit]: a continuous function vanishing to
    the right of b vanishes at b, the value f(b) = 0 used implicitly in
    Federer 2.5.18(3), p. 112. *)
Lemma vanish_right_limit (f : R -> R) (b : R) :
  continuous f -> (forall x, b < x -> f x = 0) -> f b = 0.
Proof.
move=> hf hz; have [hz0|hne] := eqVneq (f b) 0; first by [].
exfalso; have hpos : 0 < `|f b| by rewrite normr_gt0.
have [d [hd hball]] := continuity_radius_exists b hf hpos.
have hb : `|b - (b + d / 2)| < d.
  rewrite opprD addrA subrr add0r normrN gtr0_norm; lra.
have := hball _ hb; rewrite (hz (b + d / 2)); last by lra.
by rewrite subr0 ltxx.
Qed.

(** Source for [continuous_support_segment_bound]: a continuous function
    with support in {t : a <= t <= b} is bounded, the finiteness of
    sup |f| used in Federer 2.5.18(3), p. 112. *)
Lemma continuous_support_segment_bound (f : R -> R) (a b : R) :
  continuous f -> a <= b -> real_function_support f `<=` `[a, b] ->
  exists M, forall x, `|f x| <= M.
Proof.
move=> hf hab hs.
have hz := support_segment_vanish hs.
have hfb : f b = 0 := vanish_right_limit hf (fun x hx => hz x (or_intror hx)).
have hne : `[a, b] !=set0 by exists a; rewrite /= in_itv /= lexx hab.
have hcf : continuous (f : R -> R^o) := hf.
have hcn : continuous ((fun x => -1 * f x) : R -> R^o) := continuous_scale (c := -1) hf.
have [x1 [hx1 hmax1]] := continuous_compact_maximum hne (@segment_compact R a b) hcf.
have [x2 [hx2 hmax2]] := continuous_compact_maximum hne (@segment_compact R a b) hcn.
have hbb : `[a, b] b by rewrite /= in_itv /= lexx hab.
have h1 : 0 <= f x1 by have := hmax1 b hbb; rewrite hfb.
have h2 : 0 <= -1 * f x2 by have := hmax2 b hbb; rewrite hfb mulr0.
exists (Order.max (f x1) (-1 * f x2))=> x.
have [hin|hout] := pselect (`[a, b] x).
- rewrite ler_norml; apply/andP; split.
  + rewrite lerNl le_max; apply/orP; right.
    by have := hmax2 x hin; rewrite mulN1r.
  + by rewrite le_max (hmax1 x hin).
- have hx0 : f x = 0.
    apply: hz; move: hout; rewrite /= in_itv /= => /negP; rewrite negb_and -!ltNge.
    by move=> /orP[h|h]; [left|right].
  by rewrite hx0 normr0 le_max h1.
Qed.

End SupportFacts.

Section DistributionFunction.
Variable R : realType.
Variable X : choiceType.
Variables (phi : set X -> \bar R) (u : X -> R).
Hypothesis hm : is_measure phi.
Hypothesis hfin : (phi setT < +oo)%E.
Hypothesis hu : is_measure_measurable_function phi (partial_function_total (u : X -> real_line_metric R)).
Local Notation KR := (@compactly_supported_continuous_functions R R).

(** Source for [distribution_function]: the phi distribution function
    g(t) = phi{x : u(x) < t} of u, Federer 2.5.18(3), p. 112; the finite
    measure is read as a real number. *)
Definition distribution_function (t : R) : R := fine (phi [set x | u x < t]).

(** Source for [sublevel_measurable]: {x : u(x) < t} is phi measurable,
    the open inverse image clause of 2.3.2 used in Federer 2.5.18(3),
    p. 112. *)
Lemma sublevel_measurable (t : R) : measure_measurable phi [set x | u x < t].
Proof.
have hU : open [set s : real_line_metric R | s < t] by exact: (@open_lt R t).
have := measurable_function_open_preimage hu hU.
by rewrite partial_function_total_preimage.
Qed.

(** Source for [sublevel_finite]: {x : u(x) < t} has finite measure
    because phi(X) < oo, Federer 2.5.18(3), p. 112. *)
Lemma sublevel_finite (t : R) : phi [set x | u x < t] \is a fin_num.
Proof.
rewrite ge0_fin_numE ?(measure_nonnegative hm) //.
exact: le_lt_trans (measure_mono hm (subsetT _)) hfin.
Qed.

(** Source for [distribution_function_nondecreasing]: g is
    nondecreasing, Federer 2.5.18(3), p. 112. *)
Theorem distribution_function_nondecreasing (s t : R) :
  s <= t -> distribution_function s <= distribution_function t.
Proof.
move=> hst; apply: fine_le; [exact: sublevel_finite|exact: sublevel_finite|].
by apply: (measure_mono hm)=> x /= hx; exact: lt_le_trans hx hst.
Qed.

(** Source for [distribution_function_variation]: g has finite variation
    on every segment, so that the integrals int_a^b f dg of 2.5.17 are
    defined, Federer 2.5.18(3), p. 112. *)
Lemma distribution_function_variation :
  curve_locally_finite_variation (distribution_function : R -> real_line_metric R).
Proof. exact (monotone_locally_finite_variation distribution_function_nondecreasing). Qed.

(** Source for [cell_set]: the set {x : t <= u(x) < t'} whose measure is
    g(t') - g(t), Federer 2.5.18(3), p. 112. *)
Definition cell_set (t t' : R) : set X := [set x | t <= u x /\ u x < t'].

(** Source for [cell_indicator]: the characteristic function of
    {x : t <= u(x) < t'}, Federer 2.5.18(3), p. 112, and 2.2.14,
    p. 70. *)
Definition cell_indicator (t t' : R) (x : X) : R :=
  if (t <= u x) && (u x < t') then 1 else 0.

(** Source for [cell_indicator_characteristic]: the two-case laws of
    the characteristic function, Federer 2.2.14, p. 70, for the cell of
    Federer 2.5.18(3), p. 112. *)
Lemma cell_indicator_characteristic (t t' : R) :
  is_characteristic_function (cell_set t t') (cell_indicator t t').
Proof.
constructor=> x; rewrite /cell_set /cell_indicator /=.
- by move=> [h1 h2]; rewrite h1 h2.
- move=> hx; case: ifP=> // /andP[h1 h2]; exfalso; exact: hx (conj h1 h2).
Qed.

(** Source for [cell_set_difference]: {x : t <= u(x) < t'} is the
    difference of two sublevel sets, Federer 2.5.18(3), p. 112. *)
Lemma cell_set_difference (t t' : R) :
  cell_set t t' = [set x | u x < t'] `\` [set x | u x < t].
Proof.
apply/seteqP; split=> x /=.
- by move=> [h1 h2]; split=> //; apply/negP; rewrite -leNgt.
- by move=> [h1 /negP h2]; split=> //; rewrite leNgt.
Qed.

(** Source for [cell_set_measurable]: {x : t <= u(x) < t'} is phi
    measurable, Federer 2.5.18(3), p. 112. *)
Lemma cell_set_measurable (t t' : R) : measure_measurable phi (cell_set t t').
Proof.
rewrite cell_set_difference.
exact (measure_measurable_difference hm (sublevel_measurable t') (sublevel_measurable t)).
Qed.

(** Source for [cell_set_finite]: {x : t <= u(x) < t'} has finite
    measure, Federer 2.5.18(3), p. 112. *)
Lemma cell_set_finite (t t' : R) : phi (cell_set t t') \is a fin_num.
Proof.
rewrite ge0_fin_numE ?(measure_nonnegative hm) //.
exact: le_lt_trans (measure_mono hm (subsetT _)) hfin.
Qed.

(** Source for [cell_set_measure]: phi{x : t <= u(x) < t'} = g(t') - g(t)
    for t <= t', by the Caratheodory splitting of {x : u(x) < t'} by the
    measurable set {x : u(x) < t}, Federer 2.5.18(3), p. 112, and 2.1.2,
    p. 54. *)
Lemma cell_set_measure (t t' : R) :
  t <= t' -> fine (phi (cell_set t t')) = distribution_function t' - distribution_function t.
Proof.
move=> htt'.
have hBS : [set x | u x < t] `<=` [set x | u x < t'].
  by move=> x /= hx; exact: lt_le_trans hx htt'.
have hsplit := sublevel_measurable t [set x | u x < t'].
rewrite (setIidr hBS) -cell_set_difference in hsplit.
have hfinS := sublevel_finite t'.
have hfinB := sublevel_finite t.
have hfinC := cell_set_finite t t'.
rewrite /distribution_function.
have := congr1 fine hsplit; rewrite fineD // => ->; ring.
Qed.

(** Source for [cell_term_integral]: the phi integral of c times the
    characteristic function of {x : t <= u(x) < t'} is c [g(t') - g(t)],
    Federer 2.5.18(3), p. 112, and 2.4.5, p. 83. *)
Lemma cell_term_integral (c t t' : R) :
  t <= t' ->
  is_measure_integral phi (real_total_integrand (fun x => c * cell_indicator t t' x))
    (c * (distribution_function t' - distribution_function t))%:E.
Proof.
move=> htt'.
have hi := measure_characteristic_integral hm (cell_indicator_characteristic t t')
  (cell_set_measurable t t').
rewrite -(fineK (cell_set_finite t t')) (cell_set_measure htt') in hi.
exact (real_total_integral_scale hm c hi).
Qed.

(** Source for [cell_sum]: the simple function
    sum_j f(u_j) chi_{x : t_j <= u(x) < t_{j+1}} attached to a sequence
    t_1 <= u_1 <= t_2 <= u_2 <= ... of 2.5.17, whose phi integral is the
    Riemann-Stieltjes sum of f with respect to g, Federer 2.5.18(3),
    p. 112. *)
Fixpoint cell_sum (f : R -> R) (w : seq R) (x : X) : R :=
  match w with
  | t :: v :: ((t' :: _) as rest) => f v * cell_indicator t t' x + cell_sum f rest x
  | _ => 0
  end.
Arguments cell_sum : simpl never.

(** Source for [cell_sum_cons]: one step of the recursion defining the
    simple function, Federer 2.5.18(3), p. 112. *)
Lemma cell_sum_cons (f : R -> R) (t v t' : R) (rest : seq R) (x : X) :
  cell_sum f (t :: v :: t' :: rest) x = f v * cell_indicator t t' x + cell_sum f (t' :: rest) x.
Proof. by []. Qed.

(** Source for [cell_sum_integral]: the phi integral of the simple
    function is the Riemann-Stieltjes sum, Federer 2.5.18(3), p. 112. *)
Lemma cell_sum_integral (f : R -> R) (w : seq R) :
  sorted <=%O w ->
  is_measure_integral phi (real_total_integrand (cell_sum f w))
    (stieltjes_sum f distribution_function w)%:E.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|v [|t' rest]]] hsize hs.
- exact (real_total_zero_integral hm).
- exact (real_total_zero_integral hm).
- exact (real_total_zero_integral hm).
move: hs=> /= /andP[htv /andP[hvt' hrest]].
have htt' : t <= t' := le_trans htv hvt'.
have hsize' : (size (t' :: rest) < n)%N by move: hsize; rewrite /= !ltnS; exact: ltnW.
have hterm := cell_term_integral (f v) htt'.
have hih := ih _ hsize' hrest.
have hsum := real_total_integral_add hm hterm hih.
exact: hsum.
Qed.

(** Source for [cell_sum_estimate]: the simple function vanishes where
    u lies outside [t_1, t_{n+1}) and differs from f o u by at most the
    oscillation of f over cells of length below delta elsewhere, Federer
    2.5.18(3), p. 112, with the uniform continuity of 2.5.17, p. 111. *)
Lemma cell_sum_estimate (f : R -> R) (d om : R) (w : seq R) (x : X) :
  sorted <=%O w -> odd (size w) -> tagged_mesh_lt d w ->
  (forall s s', head 0 w <= s <= last 0 w -> head 0 w <= s' <= last 0 w ->
    `|s - s'| < d -> `|f s - f s'| <= om) ->
  (u x < head 0 w -> cell_sum f w x = 0) /\
  (last 0 w <= u x -> cell_sum f w x = 0) /\
  (head 0 w <= u x < last 0 w -> `|cell_sum f w x - f (u x)| <= om).
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|v [|t' rest]]] hsize hs hodd hmesh hmod.
- split=> //; split=> // /andP[h1 h2]; by move: (le_lt_trans h1 h2); rewrite ltxx.
- split=> //; split=> // /andP[h1 h2]; by move: (le_lt_trans h1 h2); rewrite ltxx.
- by [].
move: hs=> /= /andP[htv /andP[hvt' hrest]].
have htt' : t <= t' := le_trans htv hvt'.
rewrite tagged_mesh_lt_cons in hmesh; move: hmesh=> /andP[hmesh1 hmesh2].
have hsize' : (size (t' :: rest) < n)%N by move: hsize; rewrite /= !ltnS; exact: ltnW.
have hodd' : odd (size (t' :: rest)) by move: hodd; rewrite /= negbK.
have /andP[_ ht'b] := sorted_mem_bounds (s := t' :: rest) hrest (mem_head t' rest).
rewrite /= in ht'b hmod.
have hmod' : forall s s', t' <= s <= last t' rest -> t' <= s' <= last t' rest ->
    `|s - s'| < d -> `|f s - f s'| <= om.
  move=> s s' /andP[h1 h2] /andP[h3 h4]; apply: hmod.
  - by rewrite (le_trans htt' h1) h2.
  - by rewrite (le_trans htt' h3) h4.
have [ih1 [ih2 ih3]] := ih _ hsize' hrest hodd' hmesh2 hmod'.
rewrite cell_sum_cons /cell_indicator.
split; [|split].
- move=> hxt.
  have -> : (t <= u x) && (u x < t') = false by rewrite leNgt hxt.
  rewrite mulr0 add0r; apply: ih1; exact: lt_le_trans hxt htt'.
- move=> hbx.
  have -> : (u x < t') = false by rewrite ltNge (le_trans ht'b hbx).
  rewrite andbF mulr0 add0r; exact: ih2 hbx.
- move=> /andP[htx hxb].
  have [hxt'|hxt'] := ltP (u x) t'.
  + rewrite htx /= mulr1 (ih1 hxt') addr0.
    apply: hmod.
    - by rewrite htv (le_trans hvt' ht'b).
    - by rewrite htx (ltW hxb).
    - rewrite ltr_norml; apply/andP; split; lra.
  + by rewrite andbF mulr0 add0r; apply: ih3; rewrite /= hxt' hxb.
Qed.

(** Source for [constant_integral]: the phi integral of a constant c is
    c phi(X), Federer 2.4.5, p. 83, used in Federer 2.5.18(3), p. 112. *)
Lemma constant_integral (c : R) :
  is_measure_integral phi (real_total_integrand (fun _ : X => c)) (c * fine (phi setT))%:E.
Proof.
have hchar : is_characteristic_function setT (fun _ : X => (1 : R)).
  by constructor=> [x _ //|x hx]; exfalso; exact: hx I.
have hi := measure_characteristic_integral hm hchar (measure_measurable_whole hm).
have hfinT : phi setT \is a fin_num by rewrite ge0_fin_numE ?(measure_nonnegative hm).
rewrite -(fineK hfinT) in hi.
have := real_total_integral_scale hm c hi.
have -> : (fun x : X => c * 1) = (fun _ : X => c) by apply: funext=> x; rewrite mulr1.
by [].
Qed.

(** Source for [real_total_integral_le]: comparison of the integrals of
    two pointwise ordered real functions, Federer 2.4.4(2), p. 82, used
    in Federer 2.5.18(3), p. 112. *)
Lemma real_total_integral_le (F G : X -> R) (r s : R) :
  is_measure_integral phi (real_total_integrand F) r%:E ->
  is_measure_integral phi (real_total_integrand G) s%:E ->
  (forall x, F x <= G x) -> r <= s.
Proof.
move=> hF hG hle.
have := measure_integral_monotone hm hF hG (real_total_pointwise_order_almost hm hle).
by rewrite lee_fin.
Qed.

(** Source for [bounded_measurable_integral]: a bounded phi measurable
    real function on a space of finite measure has a finite integral,
    Federer 2.4.4(2), p. 82, by comparison with the constants
    -M and M, used in Federer 2.5.18(3), p. 112. *)
Lemma bounded_measurable_integral (F : X -> R) (M : R) :
  is_measure_measurable_function phi (real_total_integrand F) ->
  (forall x, `|F x| <= M) ->
  exists r : R, is_measure_integral phi (real_total_integrand F) r%:E.
Proof.
move=> hF hM.
have hC := constant_integral M.
have hC' := constant_integral (- M).
have hle : function_le F (fun _ : X => M).
  by move=> x; have := hM x; rewrite ler_norml=> /andP[_ h].
have hge : function_le (fun _ : X => - M) F.
  by move=> x; have := hM x; rewrite ler_norml=> /andP[h _].
have [a [b [ha [hb hab]]]] := measurable_integral_comparison hm hF hC.1
  (real_total_pointwise_order_almost hm hle) (or_introl (ex_intro _ _ (conj hC (ltry _)))).
rewrite (measure_integral_unique hb hC) in hab.
have [a' [b' [ha' [hb' ha'b']]]] := measurable_integral_comparison hm hC'.1 hF
  (real_total_pointwise_order_almost hm hge)
  (or_introl (ex_intro _ _ (conj ha (le_lt_trans hab (ltry _))))).
rewrite (measure_integral_unique ha' hC') (measure_integral_unique hb' ha) in ha'b'.
have hafin : a \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr _) ha'b'.
  - exact: le_lt_trans hab (ltry _).
by exists (fine a); rewrite fineK.
Qed.

(** Source for [distribution_function_integral]: the identity
    int (f o u) dphi = int_a^b f dg for f in K(R) with
    spt f subset {t : a <= t <= b}, Federer 2.5.18(3), p. 112. The phi
    integral of f o u exists and equals the Riemann-Stieltjes integral
    of 2.5.17. *)
Theorem distribution_function_integral (f : R -> R) (a b : R) :
  KR f -> a <= b -> real_function_support f `<=` `[a, b] ->
  is_measure_integral phi (real_total_integrand (fun x => f (u x)))
    (stieltjes_integral distribution_function f a b)%:E.
Proof.
move=> hf hab hs.
have hcont : continuous f := KR_continuous hf.
have hz := support_segment_vanish hs.
have hfb : f b = 0 := vanish_right_limit hcont (fun x hx => hz x (or_intror hx)).
have [M hM] := continuous_support_segment_bound hcont hab hs.
have hmeas : is_measure_measurable_function phi (real_total_integrand (fun x => f (u x))) :=
  measurable_partial_real_embedding hm (measurable_total_borel_postcomposition hm hu
    (continuous_borel_function (f := f : real_line_metric R -> real_line_metric R) hcont)).
have [r hr] := bounded_measurable_integral hmeas (fun x => hM (u x)).
suff -> : stieltjes_integral distribution_function f a b = r by [].
symmetry; apply: (stieltjes_integral_unique distribution_function_variation hcont hab).
move=> e he.
have hT : 0 <= fine (phi setT) by rewrite fine_ge0 // (measure_nonnegative hm).
have hT1 : 0 < fine (phi setT) + 1 by lra.
pose om := e / 2 / (fine (phi setT) + 1).
have hom : 0 < om by rewrite /om; apply: divr_gt0=> //; apply: divr_gt0=> //; lra.
have homT : om * (fine (phi setT) + 1) = e / 2 by rewrite /om mulfVK // (lt0r_neq0 hT1).
have [d [hd hmod]] := segment_uniform_continuity a b hcont hom.
exists d; split=> // w hw hmesh.
have hhead : head 0 w = a := tagged_partition_head0 hw.
have hlast : last 0 w = b := tagged_partition_last0 hw.
have hmod' : forall s s', head 0 w <= s <= last 0 w -> head 0 w <= s' <= last 0 w ->
    `|s - s'| < d -> `|f s - f s'| <= om.
  by move=> s s'; rewrite hhead hlast=> h1 h2 h3; exact: ltW (hmod s s' h1 h2 h3).
have hpt : forall x, `|cell_sum f w x - f (u x)| <= om.
  move=> x; have [c1 [c2 c3]] := cell_sum_estimate x hw.1 hw.2.1 hmesh hmod'.
  rewrite hhead hlast in c1 c2 c3.
  have [hxa|hxa] := ltP (u x) a.
  - by rewrite (c1 hxa) (hz _ (or_introl hxa)) subr0 normr0; exact: ltW hom.
  have [hxb|hxb] := ltP (u x) b.
  - by apply: c3; rewrite hxa hxb.
  rewrite (c2 hxb).
  have -> : f (u x) = 0.
    have [h|h|h] := ltgtP b (u x).
    + exact (hz _ (or_intror h)).
    + by move: (lt_le_trans h hxb); rewrite ltxx.
    + by rewrite -h hfb.
  by rewrite subr0 normr0; exact: ltW hom.
have hS := cell_sum_integral f hw.1.
have hup := real_total_integral_add hm hr (constant_integral om).
have hdown := real_total_integral_subtract hm hr (constant_integral om).
have h1 : stieltjes_sum f distribution_function w <= r + om * fine (phi setT).
  apply: (real_total_integral_le hS hup)=> x /=.
  by have := hpt x; rewrite ler_norml=> /andP[_ h]; lra.
have h2 : r - om * fine (phi setT) <= stieltjes_sum f distribution_function w.
  apply: (real_total_integral_le hdown hS)=> x /=.
  by have := hpt x; rewrite ler_norml=> /andP[h _]; lra.
have h3 : om * fine (phi setT) <= om * (fine (phi setT) + 1).
  by rewrite ler_pM2l // lerDl ler01.
rewrite homT in h3.
rewrite ltr_norml; apply/andP; split; lra.
Qed.

End DistributionFunction.
