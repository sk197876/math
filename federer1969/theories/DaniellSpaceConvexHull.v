(** Federer (1969), 2.5.19, p. 113: if X is a compact Hausdorff space, the
    closure of the convex hull of the image of delta equals the set of those
    monotone Daniell integrals on K(X) whose associated measures have the
    value 1 at X. A Daniell integral in the closure is additive,
    homogeneous, monotone and has the value 1 at the constant function 1,
    because these are closed conditions on finitely many values; it is then
    a Daniell integral by 2.5.13, p. 106. Conversely a monotone Daniell
    integral lambda with lambda(1) = 1 is approximated on finitely many
    members of K(X) by sum_x lambda(g_x) delta_x, where the g_x form a
    finite partition of unity subordinate to a cover of X by sets on which
    the given members oscillate little, as in 2.5.14, p. 108. The value at X
    of a measure representing lambda is lambda(1). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeLaws
  FunctionLatticeSeminormUP FunctionLatticeRegularityUP ExtendedRealOrderLimit
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralAlgebra DaniellIntegralNegation
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportProducts
  CompactSupportRieszRepresentation CompactFiniteCover FiniteCompactPartitionUP
  FiniteCompactPartitionSealed CharacteristicFunctionUP MeasureUP MeasureSplit PartialFunctionUP
  PartialFunctionBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureExtendedCharacteristicIntegral SummableRealFunctionUP RealIntegralFunctionalUP
  RegularDaniellRepresentation SubtypeCompactHausdorff DaniellSpaceWeakTopology DaniellSpaceEmbedding
  DaniellSpaceCompactness DaniellSpaceCompactSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ConvexCombinations.
Variable R : realType.
Variable X : choiceType.
Variable L : set (X -> R).

(** Source for [point_evaluation_convex_hull]: the convex hull of the
    image of delta, Federer 2.5.19, p. 113: the finite combinations
    sum_j c_j delta_{x_j} with c_j >= 0 and sum_j c_j = 1. *)
Definition point_evaluation_convex_hull : set ((X -> R) -> R) :=
  [set A | exists s : seq (R * X), (forall p, p \in s -> 0 <= p.1) /\ \sum_(p <- s) p.1 = 1 /\
    A = fun f => \sum_(p <- s) p.1 * f p.2].

(** Source for [convex_hull_add]: convex combinations of point
    evaluations are additive, supporting Federer 2.5.19, p. 113. *)
Lemma convex_hull_add (B : (X -> R) -> R) (f g : X -> R) :
  point_evaluation_convex_hull B -> B (fun x => f x + g x) = B f + B g.
Proof. by move=> [s [_ [_ ->]]] /=; rewrite -big_split; apply: eq_bigr=> p _; rewrite mulrDr. Qed.

(** Source for [convex_hull_scale]: convex combinations of point
    evaluations are homogeneous, supporting Federer 2.5.19, p. 113. *)
Lemma convex_hull_scale (B : (X -> R) -> R) (c : R) (f : X -> R) :
  point_evaluation_convex_hull B -> B (fun x => c * f x) = c * B f.
Proof. by move=> [s [_ [_ ->]]] /=; rewrite mulr_sumr; apply: eq_bigr=> p _; rewrite mulrCA. Qed.

(** Source for [convex_hull_monotone]: convex combinations of point
    evaluations preserve order, supporting Federer 2.5.19, p. 113. *)
Lemma convex_hull_monotone (B : (X -> R) -> R) (f g : X -> R) :
  point_evaluation_convex_hull B -> function_le f g -> B f <= B g.
Proof.
move=> [s [hs [_ ->]]] hfg /=; rewrite !big_seq; apply: ler_sum=> p hp.
by apply: ler_wpM2l; [exact: hs | exact: hfg].
Qed.

(** Source for [convex_hull_one]: convex combinations of point
    evaluations take the value 1 at the constant function 1, supporting
    Federer 2.5.19, p. 113. *)
Lemma convex_hull_one (B : (X -> R) -> R) :
  point_evaluation_convex_hull B -> B (fun _ => 1) = 1.
Proof. by move=> [s [_ [h1 ->]]] /=; rewrite -[RHS]h1; apply: eq_bigr=> p _; rewrite mulr1. Qed.

(** Source for [daniell_weak_closure_linear_le]: a linear inequality in
    finitely many values on members of L valid on a set of functionals
    remains valid on its weak closure, supporting Federer 2.5.19,
    p. 113. *)
Lemma daniell_weak_closure_linear_le (Z : set (daniell_weak_space L)) (A : (X -> R) -> R)
    (l : seq (R * (X -> R))) (c : R) :
  all (fun p : R * (X -> R) => `[< L p.2 >]) l -> closure Z A ->
  (forall B, Z B -> \sum_(p <- l) p.1 * B p.2 <= c) -> \sum_(p <- l) p.1 * A p.2 <= c.
Proof.
move=> hl hcl hZ; rewrite leNgt; apply/negP=> hlt.
pose d := \sum_(p <- l) p.1 * A p.2 - c.
have hdE : d = \sum_(p <- l) p.1 * A p.2 - c by [].
have hd : 0 < d by rewrite /d subr_gt0.
pose s := \sum_(p <- l) `|p.1|.
have hsE : s = \sum_(p <- l) `|p.1| by [].
have hs : 0 <= s by apply: sumr_ge0=> p _; exact: normr_ge0.
have hs1 : 0 < s + 1 by lra.
pose e := d / (s + 1).
have he : 0 < e by rewrite /e divr_gt0.
have hfs : forall f, f \in [seq p.2 | p <- l] -> L f.
  by move=> f /mapP [p hp ->]; apply/asboolP; exact: (allP hl p hp).
have hN := daniell_weak_box_nbhs A he hfs.
have [B [hZB hB]] := hcl _ hN.
have hle := hZ B hZB.
have hdiff : `|\sum_(p <- l) p.1 * B p.2 - \sum_(p <- l) p.1 * A p.2| <= e * s.
  rewrite -sumrB; apply: le_trans (ler_norm_sum _ _ _) _.
  rewrite hsE mulr_sumr !big_seq; apply: ler_sum=> p hpl.
  rewrite -mulrBr normrM [e * _]mulrC; apply: ler_wpM2l; first exact: normr_ge0.
  by apply: ltW; apply: hB; exact: map_f hpl.
have hes : e * s < d.
  have h1 : e * s < e * (s + 1) by rewrite ltr_pM2l // ltrDl ltr01.
  have h2 : e * (s + 1) = d by rewrite /e mulfVK // gt_eqF.
  lra.
move/ler_normlP: hdiff=> [h3 h4].
lra.
Qed.

End ConvexCombinations.

Section ConvexHull.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hh : hausdorff_space X.
Hypothesis hc : compact (@setT X).
Local Notation K := (@compactly_supported_continuous_functions R X).
(** Source for [hL]: the lattice laws of K(X), Federer 2.5.13, p. 106,
    used throughout 2.5.19, p. 113. *)
Let hL : is_function_lattice K := @compactly_supported_continuous_functions_lattice R X.
(** Source for [hl]: a compact space is locally compact, supporting the
    compact case of Federer 2.5.19, p. 113. *)
Let hl : locally_compact (@setT X) := compact_space_locally_compact hc.
(** Source for [hone]: the constant function 1 belongs to K(X) for
    compact X, Federer 2.5.19, p. 113. *)
Let hone : K (fun _ => 1) := compact_space_constant_one R hc.
(** Source for [h0]: the zero function belongs to K(X), Federer 2.5.13,
    p. 106. *)
Let h0 : K (fun _ => 0) := @compactly_supported_zero_function R X.

(** Source for [convex_hull_closure_monotone]: every member of the
    closure of the convex hull of the image of delta is a monotone
    Daniell integral on K(X) with value 1 at the constant function 1,
    the first inclusion of Federer 2.5.19, p. 113. *)
Lemma convex_hull_closure_monotone (A : (X -> R) -> R) :
  closure (@point_evaluation_convex_hull R X : set (daniell_weak_space K)) A ->
  is_monotone_daniell_integral K A /\ A (fun _ => 1) = 1.
Proof.
move=> hcl; have hone' := hone.
have hadd : forall f g, K f -> K g -> A (fun x => f x + g x) = A f + A g.
  move=> f g hf hg; have hfg := function_lattice_add hL hf hg.
  have hm1 : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (1, fun x => f x + g x); (-1, f); (-1, g)].
    by rewrite /= !asboolT.
  have hm2 : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (-1, fun x => f x + g x); (1, f); (1, g)].
    by rewrite /= !asboolT.
  have hz1 : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (1, fun x => f x + g x); (-1, f); (-1, g)]) p.1 * B p.2 <= 0.
    by move=> B hB; rewrite !big_cons big_nil /= (convex_hull_add f g hB); lra.
  have hz2 : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (-1, fun x => f x + g x); (1, f); (1, g)]) p.1 * B p.2 <= 0.
    by move=> B hB; rewrite !big_cons big_nil /= (convex_hull_add f g hB); lra.
  have h1 := daniell_weak_closure_linear_le hm1 hcl hz1.
  have h2 := daniell_weak_closure_linear_le hm2 hcl hz2.
  rewrite !big_cons big_nil /= in h1 h2; lra.
have hscale : forall c f, K f -> A (fun x => c * f x) = c * A f.
  move=> c f hf; have hcf := compactly_supported_scale c hf.
  have hm1 : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (1, fun x => c * f x); (- c, f)].
    by rewrite /= !asboolT.
  have hm2 : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (-1, fun x => c * f x); (c, f)].
    by rewrite /= !asboolT.
  have hz1 : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (1, fun x => c * f x); (- c, f)]) p.1 * B p.2 <= 0.
    move=> B hB; rewrite !big_cons big_nil /= (convex_hull_scale c f hB).
    by rewrite mul1r addr0 mulNr subrr.
  have hz2 : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (-1, fun x => c * f x); (c, f)]) p.1 * B p.2 <= 0.
    move=> B hB; rewrite !big_cons big_nil /= (convex_hull_scale c f hB).
    by rewrite mulN1r addr0 addNr.
  have h1 := daniell_weak_closure_linear_le hm1 hcl hz1.
  have h2 := daniell_weak_closure_linear_le hm2 hcl hz2.
  move: h1 h2; rewrite !big_cons big_nil /= mul1r mulN1r !addr0 mulNr.
  move: (c * A f)=> y h1 h2; lra.
have hmono : forall f g, K f -> K g -> function_le f g -> A f <= A g.
  move=> f g hf hg hfg.
  have hm : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (1, f); (-1, g)].
    by rewrite /= !asboolT.
  have hz : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (1, f); (-1, g)]) p.1 * B p.2 <= 0.
    move=> B hB; rewrite !big_cons big_nil /=.
    have := convex_hull_monotone hB hfg; lra.
  have h1 := daniell_weak_closure_linear_le hm hcl hz.
  rewrite !big_cons big_nil /= in h1; lra.
have hA1 : A (fun _ => 1) = 1.
  have hm1 : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (1, fun _ : X => (1 : R))].
    by rewrite /= !asboolT.
  have hm2 : all (fun p : R * (X -> R) => `[< K p.2 >]) [:: (-1, fun _ : X => (1 : R))].
    by rewrite /= !asboolT.
  have hz1 : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (1, fun _ : X => (1 : R))]) p.1 * B p.2 <= 1.
    by move=> B hB; rewrite big_cons big_nil /= (convex_hull_one hB) mul1r addr0.
  have hz2 : forall B, @point_evaluation_convex_hull R X B ->
      \sum_(p <- [:: (-1, fun _ : X => (1 : R))]) p.1 * B p.2 <= -1.
    by move=> B hB; rewrite big_cons big_nil /= (convex_hull_one hB) mulN1r addr0.
  have h1 := daniell_weak_closure_linear_le hm1 hcl hz1.
  have h2 := daniell_weak_closure_linear_le hm2 hcl hz2.
  move: h1 h2; rewrite !big_cons !big_nil /= mul1r mulN1r !addr0=> h1 h2.
  by apply/eqP; rewrite eq_le h1 /= -lerN2.
have hlin : is_linear_functional_on_functions K A by split; [exact: hadd | exact: hscale].
have hbound : forall u, positive_function_lattice K u ->
    exists b, forall k, lattice_positive_order_interval K u k -> A k <= b.
  by move=> u hu; exists (A u)=> k [hk [_ hku]]; exact: hmono hk hu.1 hku.
have hD : is_daniell_integral K A := compact_support_order_bounded_daniell hh hl hlin hbound.
split=> //; constructor.
- exact: hadd.
- by move=> c f _ hf; exact: hscale.
- exact: hmono.
- move=> f g hfn hg hfg; split; last exact: (daniell_integral_increasing_continuity hD hfn hg hfg).
  move=> n m hnm; rewrite lee_fin; apply: hmono (hfn n) (hfn m) _=> x.
  by have := (hfg x).1 n m hnm; rewrite lee_fin.
Qed.

(** Source for [continuity_oscillation_nbhs]: finitely many members of
    K(X) oscillate by less than e on a neighbourhood of each point,
    supporting the approximation in Federer 2.5.19, p. 113. *)
Lemma continuity_oscillation_nbhs (fs : seq (X -> R)) (e : R) (x : X) :
  0 < e -> (forall f, f \in fs -> K f) ->
  nbhs x [set y | forall f, f \in fs -> `|f y - f x| < e].
Proof.
move=> he; have hF := @nbhs_filter X x.
elim: fs=> [|f fs ih] hfs.
- by apply: (filterS _ (@filterT _ _ hF))=> y _ f; rewrite in_nil.
- have hf : K f by apply: hfs; exact: mem_head.
  have h1 : nbhs x [set y | `|f y - f x| < e].
    have hb : nbhs (f x : R) [set t : R | `|t - f x| < e] := real_ball_nbhs (f x) he.
    exact (hf.1 x _ hb).
  have h2 := ih (fun g hg => hfs g (@mem_behead _ (f :: fs) g hg)).
  apply: (filterS _ (@filterI _ _ hF _ _ h1 h2))=> y [hy1 hy2] g.
  by rewrite in_cons=> /orP[/eqP ->|hg]; [exact: hy1 | exact: hy2 g hg].
Qed.

(** Source for [convex_hull_approximation]: a monotone Daniell integral
    lambda on K(X) with lambda(1) = 1 is approximated within e on
    finitely many members of K(X) by sum_x lambda(g_x) delta_x for a
    finite partition of unity g_x of 2.5.14, p. 108; supporting
    Federer 2.5.19, p. 113. *)
Lemma convex_hull_approximation (A : (X -> R) -> R) (fs : seq (X -> R)) (e : R) :
  is_monotone_daniell_integral K A -> A (fun _ => 1) = 1 ->
  (forall f, f \in fs -> K f) -> 0 < e ->
  exists2 B, @point_evaluation_convex_hull R X B & forall f, f \in fs -> `|B f - A f| <= e.
Proof.
move=> hA hA1 hfs he.
have hD := monotone_daniell_is_daniell hA.
have hlin := daniell_compact_support_linear hD.
pose V := fun x : X => interior [set y | forall f, f \in fs -> `|f y - f x| < e].
have hVo : forall x, open (V x) by move=> x; exact: open_interior.
have hVx : forall x, V x x by move=> x; exact: continuity_oscillation_nbhs.
have hcov : [set: X] `<=` \bigcup_(x in [set: X]) V x by move=> y _; exists y.
have [F _ hFK] := @compact_open_finite_cover X X setT V setT hc (fun x _ => hVo x) hcov.
have hVF : forall x, x \in F -> open (V x) by move=> x _; exact: hVo x.
pose g := @FiniteCompactPartition.value R X X V F setT hh hl hc hVF hFK.
have hg := @FiniteCompactPartition.laws R X X V F setT hh hl hc hVF hFK.
have hgK : forall x, x \in F -> K (g x) := fun x hx => finite_compact_partition_functions hg hx.
have hsum : forall y, \sum_(x <- F) g x y = 1.
  by move=> y; exact: (@finite_compact_partition_sum _ _ _ _ _ _ _ hg y I).
have hA0 : A (fun _ => 0) = 0 := daniell_integral_zero hD h0.
have hcoef : forall x, x \in F -> 0 <= A (g x).
  move=> x hx; rewrite -hA0; apply: (monotone_daniell_integral_monotone hA h0 (hgK x hx)).
  by move=> y; have /andP[hy _] := finite_compact_partition_range hg hx y.
have hcsum : \sum_(x <- F) A (g x) = 1.
  rewrite -(daniell_finite_sum hL hD h0 hgK) -hA1; congr A.
  by apply: funext=> y; exact: hsum y.
exists (fun h => \sum_(p <- [seq (A (g x), x) | x <- F]) p.1 * h p.2).
  exists [seq (A (g x), x) | x <- F]; split; last by rewrite big_map.
  by move=> p /mapP [x hx ->]; exact: hcoef x hx.
move=> f hf; have hfK := hfs f hf; rewrite big_map.
have hfg : forall x, x \in F -> K (fun y => f y * g x y).
  by move=> x hx; exact: compact_support_continuous_multiplier hfK.1 (hgK x hx).
have hdec : A f = \sum_(x <- F) A (fun y => f y * g x y).
  rewrite -(daniell_finite_sum hL hD h0 hfg); congr A.
  by apply: funext=> y; rewrite -mulr_sumr hsum mulr1.
rewrite hdec -sumrB.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: (@le_trans _ _ (\sum_(x <- F) e * A (g x))); last by rewrite -mulr_sumr hcsum mulr1.
rewrite !big_seq; apply: ler_sum=> x hx.
have hgx := hgK x hx.
have hup : forall y, f y * g x y <= (f x + e) * g x y.
  move=> y; have /andP[hy0 _] := finite_compact_partition_range hg hx y.
  case: (eqVneq (g x y) 0)=> [->|hne]; first by rewrite !mulr0.
  apply: ler_wpM2r=> //.
  have hne' : g x y <> 0 by apply/eqP.
  have hyV : V x y :=
    finite_compact_partition_support hg hx (@subset_closure _ [set z | g x z <> 0] y hne').
  have := interior_subset hyV f hf; rewrite ltr_norml=> /andP[_ h2]; lra.
have hlow : forall y, (f x - e) * g x y <= f y * g x y.
  move=> y; have /andP[hy0 _] := finite_compact_partition_range hg hx y.
  case: (eqVneq (g x y) 0)=> [->|hne]; first by rewrite !mulr0.
  apply: ler_wpM2r=> //.
  have hne' : g x y <> 0 by apply/eqP.
  have hyV : V x y :=
    finite_compact_partition_support hg hx (@subset_closure _ [set z | g x z <> 0] y hne').
  have := interior_subset hyV f hf; rewrite ltr_norml=> /andP[h1 _]; lra.
have h1 := monotone_daniell_integral_monotone hA (hfg x hx)
  (compactly_supported_scale (f x + e) hgx) hup.
have h2 := monotone_daniell_integral_monotone hA (compactly_supported_scale (f x - e) hgx)
  (hfg x hx) hlow.
rewrite (hlin.2 _ _ hgx) mulrDl in h1.
rewrite (hlin.2 _ _ hgx) mulrBl in h2.
rewrite [A (g x) * f x]mulrC.
move: (f x * A (g x)) (e * A (g x)) h1 h2=> u v h1 h2.
rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [point_evaluation_convex_hull_closure]: for compact
    Hausdorff X the closure of the convex hull of the image of delta is
    the set of monotone Daniell integrals lambda on K(X) with
    lambda(1) = 1, Federer 2.5.19, p. 113. *)
Theorem point_evaluation_convex_hull_closure (A : (X -> R) -> R) :
  closure (@point_evaluation_convex_hull R X : set (daniell_weak_space K)) A <->
  is_monotone_daniell_integral K A /\ A (fun _ => 1) = 1.
Proof.
split; first exact: convex_hull_closure_monotone.
move=> [hA hA1].
pose D := [set p : seq (X -> R) * R | (forall f, f \in p.1 -> K f) /\ 0 < p.2].
pose S := fun p : seq (X -> R) * R => [set B : daniell_weak_space K |
  @point_evaluation_convex_hull R X B /\ forall f, f \in p.1 -> `|B f - A f| < p.2].
have hS : forall p, D p -> S p !=set0.
  move=> [fs e] [hfs he]; rewrite /= in hfs he; have he2 : 0 < e / 2 by lra.
  have [B hB hBf] := convex_hull_approximation hA hA1 hfs he2.
  exists B; split=> //= f hf; have := hBf f hf; lra.
have hF : Filter (filter_from D S).
  apply: filter_from_filter; first by exists ([::], 1); split=> //; exact: ltr01.
  move=> [fs e] [gs e'] [hfs he] [hgs he']; rewrite /= in hfs he hgs he'; exists (fs ++ gs, Order.min e e').
  - split; last by rewrite lt_min he he'.
    by move=> f; rewrite mem_cat=> /orP[/hfs|/hgs].
  - move=> B [hB hBf]; split; split=> //= f hf.
    + apply: lt_le_trans (hBf f _) _; first by rewrite mem_cat hf.
      by rewrite ge_min lexx.
    + apply: lt_le_trans (hBf f _) _; first by rewrite mem_cat hf orbT.
      by rewrite ge_min lexx orbT.
have hP : ProperFilter (filter_from D S) by apply: filter_from_proper=> // p; exact: hS.
have hcv : filter_from D S --> (A : daniell_weak_space K).
  apply/(daniell_weak_cvg K A hF)=> g hg U hU.
  move/nbhs_ballP: hU=> [e he heU].
  exists ([:: g], e); first by split=> //= f; rewrite inE=> /eqP ->.
  move=> B [_ hB]; apply: heU.
  by rewrite /ball /= distrC; exact: hB g (mem_head g [::]).
rewrite closureEcvg; exists (filter_from D S)=> //; split=> // B hB.
apply: filterS hB _; exists ([::], 1); first by split=> //; exact: ltr01.
by move=> T [hT _]; exact: hT.
Qed.

(** Source for [representing_measure_total]: a measure over compact X
    representing a functional on K(X) has the value lambda(1) at X,
    supporting the formulation by associated measures in Federer 2.5.19,
    p. 113. *)
Lemma representing_measure_total (phi : set X -> \bar R) (A : (X -> R) -> R) :
  is_measure phi -> is_real_integral_functional phi K A -> phi setT = (A (fun _ => 1))%:E.
Proof.
move=> hm hi.
have h1 := hi _ hone.
have hs : is_characteristic_function (@setT X) (fun _ : X => (1 : R)).
  by split=> [x _ //|x hx]; exfalso; exact: hx I.
have h2 := measure_total_characteristic_integral hm hs (measure_measurable_whole hm).
have h1' : is_measure_integral phi (partial_function_total (fun x : X => ((1 : R))%:E))
    (A (fun _ => 1))%:E.
  apply: (measure_integral_graph_equivalent _ h1)=> x z; split.
  - by move=> [y [<- <-]].
  - by move=> <-; exists 1.
exact: measure_integral_unique h2 h1'.
Qed.

(** Source for [point_evaluation_convex_hull_closure_measures]: the
    printed form of Federer 2.5.19, p. 113: for compact Hausdorff X the
    closure of the convex hull of the image of delta is the set of
    monotone Daniell integrals on K(X) whose associated K(X) regular
    measures have the value 1 at X. *)
Theorem point_evaluation_convex_hull_closure_measures (A : (X -> R) -> R) :
  closure (@point_evaluation_convex_hull R X : set (daniell_weak_space K)) A <->
  is_monotone_daniell_integral K A /\
    forall phi, is_measure phi -> is_real_integral_functional phi K A ->
      is_function_lattice_regular K phi -> phi setT = 1%:E.
Proof.
rewrite point_evaluation_convex_hull_closure; split.
- move=> [hA hA1]; split=> // phi hm hi _.
  by rewrite (representing_measure_total hm hi) hA1.
- move=> [hA hphi]; split=> //.
  have hne : exists f, K f by exists (fun _ => 0).
  have [phi [hm [hi [hr _]]]] := monotone_daniell_regular_representation hL hA hne.
  have := hphi phi hm hi hr; rewrite (representing_measure_total hm hi).
  by move=> [].
Qed.

End ConvexHull.
