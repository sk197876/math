(** Federer (1969), 2.5.19, p. 113: if X is a locally compact Hausdorff
    space and M : K(X) -> [0, oo), then K(X)* ∩ {mu : mu^+ + mu^- <= M} is
    compact for the weak topology. The proof maps the set into the cartesian
    product R^{K(X)} by restriction, where it lies in a product of segments,
    compact by Tychonoff's theorem; a cluster point of the image filter
    satisfies the linear and order relations of the members because these
    are closed conditions on finitely many coordinates, so it is the
    restriction of a Daniell integral by the criterion of 2.5.13, p. 106,
    and that integral is a cluster point of the original filter. The bound
    mu^+ + mu^- <= M is formulated through the abstract variation predicates
    of 2.5.5 and shown equivalent to the elementary condition mu(k) - mu(k')
    <= M(u) for k, k' in K(X) with 0 <= k, k' <= u. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeLaws
  FunctionLatticeSeminormUP DaniellIntegralUP DaniellIntegralAlgebra DaniellVariationUP
  DaniellVariation DaniellVariationFunctionals DaniellVariationBounds CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactSupportRieszRepresentation DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_ball_nbhs]: supporting open ball neighbourhood in R,
    used for the coordinate neighbourhoods in the product R^L of Federer
    2.5.19, p. 113. *)
Lemma real_ball_nbhs (R : realType) (x e : R) : 0 < e -> nbhs x [set t : R | `|t - x| < e].
Proof.
move=> he; have := nbhsx_ballx x e he; apply: filterS=> t ht.
have ht' : `|x - t| < e := ht.
by rewrite distrC in ht'.
Qed.

(** Source for [product_coordinate_nbhs]: supporting neighbourhoods in
    the cartesian product defined by finitely many coordinates, Federer
    2.5.19, p. 113. *)
Lemma product_coordinate_nbhs (R : realType) (I : eqType)
    (psi : prod_topology (fun _ : I => R)) (l : seq I) (e : R) :
  0 < e ->
  nbhs psi [set phi : prod_topology (fun _ : I => R) | forall i, i \in l -> `|phi i - psi i| < e].
Proof.
move=> he; elim: l=> [|i l ih].
- have hT : nbhs psi setT := @filterT _ _ (@nbhs_filter _ psi).
  by apply: (filterS _ hT)=> phi _ j; rewrite in_nil.
- have hi : nbhs psi [set phi : prod_topology (fun _ : I => R) | `|phi i - psi i| < e].
    have hF := @nbhs_filter _ psi.
    have hc := (@product_topology_cvg I (fun _ => R) (nbhs psi) psi hF).1 (@cvg_refl _ _) i.
    exact: (hc _ (real_ball_nbhs (psi i) he)).
  apply: (filterS _ (@filterI _ _ (@nbhs_filter _ psi) _ _ hi ih))=> phi [h1 h2] j.
  by rewrite in_cons=> /orP[/eqP ->|hj]; [exact: h1 | exact: h2 hj].
Qed.

(** Source for [product_closure_linear_le]: a linear inequality in
    finitely many coordinates valid on a set of the cartesian product
    remains valid at every point of its closure; supporting the closedness
    arguments of Federer 2.5.19, p. 113. *)
Lemma product_closure_linear_le (R : realType) (I : eqType)
    (Z : set (prod_topology (fun _ : I => R))) (psi : prod_topology (fun _ : I => R))
    (l : seq (R * I)) (c : R) :
  closure Z psi -> (forall phi, Z phi -> \sum_(p <- l) p.1 * phi p.2 <= c) ->
  \sum_(p <- l) p.1 * psi p.2 <= c.
Proof.
move=> hcl hZ; rewrite leNgt; apply/negP=> hlt.
pose d := \sum_(p <- l) p.1 * psi p.2 - c.
have hdE : d = \sum_(p <- l) p.1 * psi p.2 - c by [].
have hd : 0 < d by rewrite /d subr_gt0.
pose s := \sum_(p <- l) `|p.1|.
have hsE : s = \sum_(p <- l) `|p.1| by [].
have hs : 0 <= s by apply: sumr_ge0=> p _; exact: normr_ge0.
have hs1 : 0 < s + 1 by lra.
pose e := d / (s + 1).
have he : 0 < e by rewrite /e divr_gt0.
have hN := product_coordinate_nbhs psi [seq p.2 | p <- l] he.
have [phi [hZphi hphi]] := hcl _ hN.
have hle := hZ phi hZphi.
have hdiff : `|\sum_(p <- l) p.1 * phi p.2 - \sum_(p <- l) p.1 * psi p.2| <= e * s.
  rewrite -sumrB; apply: le_trans (ler_norm_sum _ _ _) _.
  rewrite hsE mulr_sumr !big_seq; apply: ler_sum=> p hpl.
  rewrite -mulrBr normrM [e * _]mulrC; apply: ler_wpM2l; first exact: normr_ge0.
  by apply: ltW; apply: hphi; exact: map_f hpl.
have hes : e * s < d.
  have h1 : e * s < e * (s + 1) by rewrite ltr_pM2l // ltrDl ltr01.
  have h2 : e * (s + 1) = d by rewrite /e mulfVK // gt_eqF.
  lra.
move/ler_normlP: hdiff=> [h3 h4].
lra.
Qed.

Section Compactness.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hh : hausdorff_space X.
Hypothesis hl : locally_compact (@setT X).
Local Notation K := (@compactly_supported_continuous_functions R X).
(** Source for [hL]: the lattice laws of K(X), Federer 2.5.13, p. 106,
    used throughout 2.5.19, p. 113. *)
Let hL : is_function_lattice K := @compactly_supported_continuous_functions_lattice R X.

(** Source for [compactly_supported_scale]: K(X) is closed under all real
    multiples, supporting the linearity of Daniell integrals on K(X) used
    in Federer 2.5.19, p. 113; the lattice clause of 2.5.1 covers only
    nonnegative multiples. *)
Lemma compactly_supported_scale (c : R) (f : X -> R) :
  compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun x => c * f x).
Proof.
move=> [hc hs]; split.
- move=> x; apply: (@continuousM R X (fun _ => c) f x); last exact: hc.
  exact: cvg_cst.
- by apply: (compact_support_unary_operation hs)=> x ->; rewrite mulr0.
Qed.

(** Source for [compactly_supported_opp]: K(X) is closed under negation,
    supporting Federer 2.5.19, p. 113. *)
Lemma compactly_supported_opp (f : X -> R) :
  compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun x => - f x).
Proof.
move=> hf; have := compactly_supported_scale (-1) hf.
by rewrite (_ : (fun x => -1 * f x) = (fun x => - f x)) //; apply: funext=> x; rewrite mulN1r.
Qed.

(** Source for [daniell_compact_support_opp]: a Daniell integral on K(X)
    changes sign with its argument, by additivity, supporting the
    linearity used in Federer 2.5.19, p. 113. *)
Lemma daniell_compact_support_opp (A : (X -> R) -> R) (g : X -> R) :
  is_daniell_integral K A -> compactly_supported_continuous_functions g ->
  A (fun x => - g x) = - A g.
Proof.
move=> hA hg; have hng := compactly_supported_opp hg.
have h := daniell_integral_add hA hg hng.
rewrite (_ : (fun x => g x + - g x) = (fun _ : X => (0 : R))) in h; last first.
  by apply: funext=> x; rewrite subrr.
rewrite (daniell_integral_zero hA hg) in h; lra.
Qed.

(** Source for [daniell_compact_support_linear]: a Daniell integral on
    K(X) is a linear functional, the converse of the first assertion of
    Federer 2.5.13, p. 106, used for the vector space K(X)* in 2.5.19,
    p. 113. *)
Lemma daniell_compact_support_linear (A : (X -> R) -> R) :
  is_daniell_integral K A -> is_linear_functional_on_functions K A.
Proof.
move=> hA; split; first by move=> f g hf hg; exact: (daniell_integral_add hA hf hg).
move=> c f hf; case: (lerP 0 c)=> hc; first exact: (daniell_integral_scale hA hc hf).
have hc' : 0 <= - c by rewrite oppr_ge0 ltW.
have hscale := daniell_integral_scale hA hc' hf.
have hmem : compactly_supported_continuous_functions (fun x => - c * f x) :=
  function_lattice_scale hL hc' hf.
have hopp := daniell_compact_support_opp hA hmem.
rewrite (_ : (fun x => c * f x) = (fun x => - (- c * f x))); last first.
  by apply: funext=> x; rewrite mulNr opprK.
by rewrite hopp hscale mulNr opprK.
Qed.

(** Source for [variation_bounded]: the condition mu^+ + mu^- <= M on
    K(X)+ of Federer 2.5.19, p. 113, through the variation predicates of
    2.5.5, p. 96. *)
Definition variation_bounded (M A : (X -> R) -> R) : Prop :=
  forall P Q, is_daniell_positive_variation K A P -> is_daniell_negative_variation K A Q ->
    forall u, positive_function_lattice K u -> P u + Q u <= M u.

(** Source for [variation_bounded_iff]: for a Daniell integral the
    condition mu^+ + mu^- <= M is the elementary condition
    mu(k) - mu(k') <= M(u) for all k, k' in K(X) with 0 <= k, k' <= u,
    by the supremum formulas of Federer 2.5.5, p. 96; supporting
    2.5.19, p. 113. *)
Lemma variation_bounded_iff (M A : (X -> R) -> R) :
  is_daniell_integral K A ->
  (variation_bounded M A <->
    forall u, positive_function_lattice K u -> forall k k',
      lattice_positive_order_interval K u k -> lattice_positive_order_interval K u k' ->
      A k - A k' <= M u).
Proof.
move=> hA; split.
- move=> hb u hu k k' hk hk'.
  have hP := daniell_positive_variation_specification hL hA.
  have hQ := daniell_negative_variation_specification hL hA.
  have h1 : A k <= daniell_positive_variation hL hA u := daniell_positive_variation_upper hP hu hk.
  have h2 : - A k' <= daniell_negative_variation hL hA u :=
    daniell_positive_variation_upper hQ hu hk'.
  have h3 := hb _ _ hP hQ u hu.
  lra.
- move=> hb P Q hP hQ u hu.
  have hPle : P u <= M u - Q u.
    apply: (daniell_positive_variation_least hP hu)=> k hk.
    have hQle : Q u <= M u - A k.
      apply: (daniell_positive_variation_least hQ hu)=> k' hk'.
      have := hb u hu k k' hk hk'; rewrite /=; lra.
    lra.
  lra.
Qed.

(** Source for [variation_bounded_value]: a Daniell integral with
    mu^+ + mu^- <= M satisfies |mu(f)| <= M(f^+) + M(f^-) for f in K(X),
    the coordinate bounds placing the set of Federer 2.5.19, p. 113, in
    a product of segments. *)
Lemma variation_bounded_value (M A : (X -> R) -> R) (f : X -> R) :
  is_daniell_integral K A -> variation_bounded M A ->
  compactly_supported_continuous_functions f ->
  `|A f| <= M (fun x => Order.max (f x) 0) + M (fun x => Order.max (- f x) 0).
Proof.
move=> hA hb hf.
have hel := (variation_bounded_iff M hA).1 hb.
have h0 : compactly_supported_continuous_functions (fun _ : X => (0 : R)) :=
  @compactly_supported_zero_function R X.
have hA0 : A (fun _ => 0) = 0 := daniell_integral_zero hA hf.
have hpos : forall u, positive_function_lattice K u -> `|A u| <= M u.
  move=> u hu.
  have hku : lattice_positive_order_interval K u u.
    by split; [exact: hu.1 | split; [exact: hu.2 | move=> x; exact: lexx]].
  have hk0 : lattice_positive_order_interval K u (fun _ => 0).
    by split; [exact: h0 | split; [move=> x; exact: lexx | exact: hu.2]].
  have h1 := hel u hu u (fun _ => 0) hku hk0.
  have h2 := hel u hu (fun _ => 0) u hk0 hku.
  rewrite hA0 in h1 h2; rewrite ler_norml; apply/andP; split; lra.
have hfp : positive_function_lattice K (fun x => Order.max (f x) 0).
  by split; [exact: (function_lattice_positive_part hL hf) | move=> x; rewrite le_max lexx orbT].
have hfm : positive_function_lattice K (fun x => Order.max (- f x) 0).
  by split; [exact: (function_lattice_negative_part hL hf) | move=> x; rewrite le_max lexx orbT].
have hsplit : A (fun x => Order.max (f x) 0) = A f + A (fun x => Order.max (- f x) 0).
  rewrite -(daniell_integral_add hA hf hfm.1); congr A; apply: funext=> x.
  by rewrite !maxEle; case: (lerP (f x) 0)=> h1; case: (lerP (- f x) 0)=> h2 /=; lra.
have hp := hpos _ hfp.
have hm := hpos _ hfm.
have -> : A f = A (fun x => Order.max (f x) 0) - A (fun x => Order.max (- f x) 0) by lra.
exact: le_trans (ler_normB _ _) (lerD hp hm).
Qed.

(** Source for [daniell_variation_bounded_compact]: for every M the set
    K(X)* ∩ {mu : mu^+ + mu^- <= M} is compact in the weak topology,
    Federer 2.5.19, p. 113. *)
Theorem daniell_variation_bounded_compact (M : (X -> R) -> R) :
  compact [set A : daniell_weak_space K | is_daniell_integral K A /\ variation_bounded M A].
Proof.
pose S := [set A : daniell_weak_space K | is_daniell_integral K A /\ variation_bounded M A].
move=> F hF hFS.
pose rho := @daniell_restriction R X K.
pose B := fun f : X -> R => M (fun x => Order.max (f x) 0) + M (fun x => Order.max (- f x) 0).
pose T := [set phi : prod_topology (fun _ : K => R) | forall i : K, `|phi i| <= B (val i)].
have hT : compact T.
  have h := @tychonoff [the eqType of set_type K] (fun _ => R)
    (fun i => [set t : R | `|t| <= B (val i)]).
  apply: h=> i.
  have -> : [set t : R | `|t| <= B (val i)] = `[- B (val i), B (val i)].
    by apply/seteqP; split=> t /=; rewrite in_itv /= ler_norml.
  exact: segment_compact.
have hG : ProperFilter (rho @ F) := fmap_proper_filter rho hF.
have hGT : (rho @ F) T.
  have hsub : S `<=` rho @^-1` T.
    move=> A hSA i; have [hA hb] := hSA.
    exact: (variation_bounded_value hA hb (set_valP i)).
  exact: (filterS hsub hFS).
have [psi [hpsiT hcl]] := hT _ hG hGT.
have hclS : closure (rho @` S) psi.
  have hFF : Filter F := hF.
  have hpre : F (rho @^-1` (rho @` S)) := @filterS _ F hFF _ _ (@preimage_image _ _ rho S) hFS.
  move: hcl; rewrite clusterE=> hcl; exact (hcl _ hpre).
pose ix := fun (f : X -> R) (hf : compactly_supported_continuous_functions f) =>
  (exist _ f (mem_set hf) : K).
have hmem : forall phi, (rho @` S) phi -> exists2 A, S A & forall f hf, phi (ix f hf) = A f.
  by move=> phi [A hSA <-]; exists A.
have hadd : forall f g (hf : compactly_supported_continuous_functions f)
    (hg : compactly_supported_continuous_functions g)
    (hfg : compactly_supported_continuous_functions (fun x => f x + g x)),
  psi (ix _ hfg) = psi (ix f hf) + psi (ix g hg).
  move=> f g hf hg hfg.
  have hz1 : forall phi, (rho @` S) phi ->
      \sum_(p <- [:: (1, ix _ hfg); (-1, ix f hf); (-1, ix g hg)]) p.1 * phi p.2 <= 0.
    move=> phi /hmem [A [hA _] hphi]; rewrite !big_cons big_nil /= !hphi.
    rewrite (daniell_integral_add hA hf hg); lra.
  have hz2 : forall phi, (rho @` S) phi ->
      \sum_(p <- [:: (-1, ix _ hfg); (1, ix f hf); (1, ix g hg)]) p.1 * phi p.2 <= 0.
    move=> phi /hmem [A [hA _] hphi]; rewrite !big_cons big_nil /= !hphi.
    rewrite (daniell_integral_add hA hf hg); lra.
  have h1 := product_closure_linear_le hclS hz1.
  have h2 := product_closure_linear_le hclS hz2.
  rewrite !big_cons big_nil /= in h1 h2; lra.
have hscale : forall c f (hf : compactly_supported_continuous_functions f)
    (hcf : compactly_supported_continuous_functions (fun x => c * f x)),
  psi (ix _ hcf) = c * psi (ix f hf).
  move=> c f hf hcf.
  have hz1 : forall phi, (rho @` S) phi ->
      \sum_(p <- [:: (1, ix _ hcf); (- c, ix f hf)]) p.1 * phi p.2 <= 0.
    move=> phi /hmem [A [hA _] hphi]; rewrite !big_cons big_nil /= !hphi.
    by rewrite (daniell_compact_support_linear hA).2 // mul1r addr0 mulNr subrr.
  have hz2 : forall phi, (rho @` S) phi ->
      \sum_(p <- [:: (-1, ix _ hcf); (c, ix f hf)]) p.1 * phi p.2 <= 0.
    move=> phi /hmem [A [hA _] hphi]; rewrite !big_cons big_nil /= !hphi.
    by rewrite (daniell_compact_support_linear hA).2 // mulN1r addr0 addNr.
  have h1 := product_closure_linear_le hclS hz1.
  have h2 := product_closure_linear_le hclS hz2.
  move: h1 h2; rewrite !big_cons big_nil /= mul1r mulN1r !addr0 mulNr.
  move: (c * psi (ix f hf))=> y h1 h2; lra.
have hbd : forall u (hu : positive_function_lattice K u) k k'
    (hk : lattice_positive_order_interval K u k) (hk' : lattice_positive_order_interval K u k'),
  psi (ix k hk.1) - psi (ix k' hk'.1) <= M u.
  move=> u hu k k' hk hk'.
  have hz : forall phi, (rho @` S) phi ->
      \sum_(p <- [:: (1, ix k hk.1); (-1, ix k' hk'.1)]) p.1 * phi p.2 <= M u.
    move=> phi /hmem [A [hA hb] hphi]; rewrite !big_cons big_nil /= !hphi.
    have := (variation_bounded_iff M hA).1 hb u hu k k' hk hk'; lra.
  have h1 := product_closure_linear_le hclS hz.
  rewrite !big_cons big_nil /= in h1; lra.
pose ext := fun f : X -> R =>
  if pselect (compactly_supported_continuous_functions f) is left h then psi (ix f h) else 0.
have hext : forall f (h : compactly_supported_continuous_functions f), ext f = psi (ix f h).
  move=> f h; rewrite /ext; case: pselect=> [h'|//].
  by congr psi; apply: val_inj.
have hrho : rho ext = psi.
  apply: funext=> i; rewrite /rho /daniell_restriction (hext _ (set_valP i)).
  by congr psi; apply: val_inj.
have hlin : is_linear_functional_on_functions K ext.
  split.
  - move=> f g hf hg.
    by rewrite (hext _ (function_lattice_add hL hf hg)) (hext _ hf) (hext _ hg); exact: hadd.
  - move=> c f hf.
    by rewrite (hext _ (compactly_supported_scale c hf)) (hext _ hf); exact: hscale.
have h0 : compactly_supported_continuous_functions (fun _ : X => (0 : R)) :=
  @compactly_supported_zero_function R X.
have hbound : forall u, positive_function_lattice K u ->
    exists b, forall k, lattice_positive_order_interval K u k -> ext k <= b.
  move=> u hu; exists (M u + ext (fun _ => 0))=> k hk.
  have hk0 : lattice_positive_order_interval K u (fun _ => 0).
    by split; [exact: h0 | split; [move=> x; exact: lexx | exact: hu.2]].
  have := hbd u hu k (fun _ => 0) hk hk0.
  by rewrite -(hext _ hk.1) -(hext _ hk0.1); lra.
have hD : is_daniell_integral K ext := compact_support_order_bounded_daniell hh hl hlin hbound.
have hvb : variation_bounded M ext.
  apply/(variation_bounded_iff M hD)=> u hu k k' hk hk'.
  by rewrite (hext _ hk.1) (hext _ hk'.1); exact: hbd.
exists ext; split; first by split.
move=> A N hFA hN.
rewrite nbhsE in hN; move: hN=> [U [hUo hUx] hUN].
case: hUo=> V hV hVU.
have hV' : nbhs psi V.
  apply: open_nbhs_nbhs; split=> //.
  by rewrite -hVU in hUx; rewrite -hrho; exact: hUx.
have := hcl (rho @` A) V (filterS (@preimage_image _ _ rho A) hFA) hV'.
move=> [phi [[a hAa hphia] hVphi]].
exists a; split=> //; apply: hUN; rewrite -hVU.
by rewrite -hphia in hVphi; exact hVphi.
Qed.

End Compactness.
