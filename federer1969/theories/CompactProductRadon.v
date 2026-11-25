(** Federer (1969), 2.7.16, printed p. 141, example (7): "hence gamma =
    xi_#(theta_n x L^{n-m}) is a Radon measure over X". The argument
    presupposes that the cartesian product theta_n x L^{n-m} of 2.6.1, p.
    114, is a Radon measure over O(n) x R^{n-m}, which Federer does not
    state. This module proves it in the generality needed: if X is a compact
    Hausdorff space and Y a locally compact Hausdorff space, both with
    countable bases, Y is covered by an increasing sequence of open sets
    with compact closures, and alpha, beta are Borel regular measures
    representing monotone Daniell integrals A, B on K(X), K(Y), then alpha x
    beta is a Radon measure over X x Y (2.2.5, p. 62) and represents the
    iterated integral h |-> B_y[A_x h(x, y)] on K(X x Y). The proof: alpha x
    beta is Borel regular by 2.6.5, p. 120 (product_measure_borel_regular;
    the Radon measure rho representing that functional (2.5.14, p. 107)
    agrees with alpha x beta on open sets by 2.5.3, p. 94, since open sets
    are increasing limits of strict levels of members of K(X x Y) when there
    is a countable base (2.5.14). A Borel regular measure agreeing with a
    Radon measure on open sets equals it (radon_agreement): on compact sets
    by subtraction from open sets of finite measure, on Borel sets by inner
    approximation (2.2.5, p. 63) and continuity from below (2.1.3(4), p.
    55), and on all sets by Borel regularity and outer regularity. A compact
    subset of a pseudometric space, such as O(n) in Hom(R^n, R^n), has a
    countable relative base (compact_subset_relative_base). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology cardinality.
From mathcomp Require Import finmap.
From Federer Require Import ArchimedeanReciprocal CountableOpenBaseUP CountableDefaultEnumeration CompactFiniteCover
  ProductCountableBaseSealed TopologicalProductMaps SubtypeCompactHausdorff AffineGroupTopology
  MeasureUP BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity ProductMeasure
  ProductBorelRegularity CompactSupportFunctionUP DaniellIntegralUP MonotoneDaniellIntegralUP
  DaniellIntegralNegation RealIntegralFunctionalUP DaniellProductUP IteratedCompactDaniell
  IteratedCompactFunctionalAlgebra DaniellProductMonotone DaniellProductRepresentation
  CompactSupportRadonRepresentation RepresentingMeasureComparison MeasureBasic MeasureContinuityBelow
  TopologicalBorel RadonCompactApproximation CompactSupportFunctionLattice CompactSupportOpenBase
  ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactSubsetBase.
Variable R : realType.
Variable T : pseudoMetricType R.
Variable K : set T.
Hypothesis hK : compact K.

(** Source for [compact_subset_relative_base]: a compact subset K of a
    pseudometric space has a countable family of open sets U_i such that
    every open V containing a point x of K contains some U_i containing
    x, supporting the countable base of O(n), a compact subset of
    Hom(R^n, R^n), used for theta_n x L^{n-m} in Federer 2.7.16, p. 141.
    Supporting lemma: for each k the interiors of the balls of radius
    1/(k+1) with centres in K have a finite subcover F_k of K, and the
    interiors of the balls B(z, 1/(k+1)), z in F_k, are the U_i. *)
Lemma compact_subset_relative_base : exists U : nat -> set T, (forall i, open (U i)) /\
  forall V, open V -> forall x, K x -> V x -> exists i, U i x /\ U i `<=` V.
Proof.
pose r (k : nat) : R := (k.+1%:R)^-1.
have hr k : 0 < r k by rewrite invr_gt0 ltr0n.
have hcov k : finite_subset_cover K (fun z : T => (ball z (r k))°) K.
  apply: compact_open_finite_cover=> //; first by move=> z _; exact: open_interior.
  move=> x hx; exists x=> //; rewrite /interior /=; exact: nbhsx_ballx.
pose F k := s2val (cid2 (hcov k)).
have hF k : K `<=` cover [set` F k] (fun z : T => (ball z (r k))°) := s2valP' (cid2 (hcov k)).
pose D := \bigcup_(k in [set: nat]) ((fun z : T => (ball z (r k))°) @` [set` F k]).
have hD : countable D.
  apply: bigcup_countable; first exact: countableP.
  move=> k _; apply: finite_set_countable; apply: finite_image; exact: finite_fset.
have [u [hu1 hu2]] := countable_default_enumeration set0 hD.
exists u; split.
- move=> j; case: (hu1 j)=> [[k _ [z _ <-]]|->]; [exact: open_interior|exact: open0].
- move=> V hV x hKx hx.
  have /nbhs_ballP [e he hxe] : nbhs x V by rewrite openE in hV; exact: hV x hx.
  have [k hk] : exists k : nat, r k + r k < e.
    have he2 : 0 < e / 2 by rewrite divr_gt0.
    have [k hk] := real_reciprocal_below he2.
    by exists k; rewrite (splitr e); apply: ltrD.
  have [z hz hxz] := hF k x hKx.
  have hDz : D (ball z (r k))° by exists k=> //; exists z.
  have [j hj] := hu2 _ hDz.
  exists j; split; first by rewrite hj.
  rewrite hj=> y hy; apply: hxe.
  have h1 : ball x (r k) z by apply: ball_sym; exact: interior_subset hxz.
  have h2 : ball z (r k) y := interior_subset hy.
  apply: (@le_ball _ _ x (r k + r k) e); first exact: ltW.
  exact: ball_triangle h1 h2.
Qed.

End CompactSubsetBase.

Section RadonComparison.
Local Open Scope ereal_scope.
Variable R : realType.
Variable T : topologicalType.
Variables (phi rho : set T -> \bar R).
Hypotheses (hphi : is_measure phi) (hrho : is_measure rho).
Hypothesis hT : hausdorff_space T.
Hypothesis hrr : is_radon_measure rho.
Hypothesis hpr : is_borel_regular_measure phi.
Variable W : nat -> set T.
Hypotheses (hWo : forall k, open (W k)) (hWc : forall k, exists2 C, compact C & W k `<=` C)
  (hWinc : forall i j, (i <= j)%N -> W i `<=` W j) (hWT : forall x, exists k, W k x).
Hypothesis heq : forall V, open V -> phi V = rho V.

(** Source for [radon_agreement_compact]: phi(K) = rho(K) for compact K,
    supporting the Radon property of theta_n x L^{n-m} in Federer
    2.7.16, p. 141: K lies in an open V with rho(V) < oo (2.2.5, p. 62),
    and phi(V ~ K) = rho(V ~ K) since V ~ K is open. Supporting lemma. *)
Lemma radon_agreement_compact K : compact K -> phi K = rho K.
Proof.
move=> hK.
have hKc : closed K := compact_closed hT hK.
have hKphi := borel_regular_borel_measurable hphi hpr (closed_borel_set hKc).
have hKrho := radon_compact_measurable hrho hrr hK.
have [V [hV hKV hVf]] : exists V, [/\ open V, K `<=` V & rho V < +oo].
  apply: contrapT=> hn.
  have : +oo <= rho K.
    apply: (radon_outer_greatest hrr)=> V hV hKV.
    rewrite leye_eq; apply/eqP; apply: contrapT=> hf; apply: hn; exists V; split=> //.
    by rewrite ltey; exact/eqP.
  by rewrite leye_eq=> /eqP he; have := radon_compact_finite hrr hK; rewrite he ltxx.
have hVK : open (V `\` K) by rewrite setDE; apply: openI=> //; exact: closed_openC.
have hd : rho (V `\` K) \is a fin_num.
  rewrite ge0_fin_numE ?(measure_nonnegative hrho) //.
  by apply: le_lt_trans hVf; apply: (measure_mono hrho); move=> x [].
have hI : V `&` K = K by apply/seteqP; split=> x; [move=> []|move=> hx; split=> //; exact: hKV].
have e1 : phi V = phi K + phi (V `\` K) by rewrite (hKphi V) hI.
have e2 : rho V = rho K + rho (V `\` K) by rewrite (hKrho V) hI.
have e3 : phi K + rho (V `\` K) = rho K + rho (V `\` K).
  by rewrite -e2 -(heq hV) e1 (heq hVK).
by rewrite -(addeK (phi K) hd) e3 addeK.
Qed.

(** Source for [radon_agreement_upper]: phi(S) <= rho(S) for every S,
    by the outer regularity of rho (2.2.5, p. 62). Supporting lemma for
    Federer 2.7.16, p. 141. *)
Lemma radon_agreement_upper S : phi S <= rho S.
Proof.
apply: (radon_outer_greatest hrr)=> V hV hSV.
by rewrite -(heq hV); exact: (measure_mono hphi).
Qed.

(** Source for [radon_agreement_borel]: rho(B) <= phi(B) for Borel B,
    by inner approximation of B cap W_k by compact sets (2.2.5, p. 63)
    and continuity from below (2.1.3(4), p. 55). Supporting lemma for
    Federer 2.7.16, p. 141. *)
Lemma radon_agreement_borel B : borel_set B -> rho B <= phi B.
Proof.
move=> hB.
have hrB := radon_borel_regular hrho hrr.
pose F k := B `&` W k.
have hF k : measure_measurable rho (F k).
  apply: (borel_regular_borel_measurable hrho hrB).
  have -> : F k = B `\` (~` W k) by rewrite /F setDE setCK.
  apply: borel_set_difference=> //; apply: closed_borel_set; exact: open_closedC (hWo k).
have hFk k : rho (F k) <= phi B.
  have [C hC hWC] := hWc k.
  have hfin : rho (F k) < +oo.
    apply: le_lt_trans (radon_compact_finite hrr hC); apply: (measure_mono hrho).
    by move=> x [_ hx]; exact: hWC.
  apply/lee_addgt0Pr=> e he.
  have [K [hK [hKF hKe]]] := radon_compact_approximation hrho hrr (hF k) hfin he.
  have hKm := radon_compact_measurable hrho hrr hK.
  have hI : F k `&` K = K by apply/seteqP; split=> x; [move=> []|move=> hx; split=> //; exact: hKF].
  rewrite (hKm (F k)) hI -(radon_agreement_compact hK).
  apply: leeD; last exact: ltW.
  by apply: (measure_mono hphi)=> x /hKF [].
have hinc i j : (i <= j)%N -> F i `<=` F j.
  by move=> hij x [hx hw]; split; [exact: hx|apply: (hWinc hij); exact: hw].
have [_ [hlo _]] := measure_continuity_below hrho hF hinc.
have hU : \bigcup_k F k = B.
  apply/seteqP; split=> x; first by move=> [k _ []].
  by move=> hx; have [k hk] := hWT x; exists k.
rewrite hU in hlo.
apply: contrapT=> /negP; rewrite -ltNge=> hlt.
have [N hN] := hlo _ hlt.
by have := hN N (leqnn N); rewrite ltNge (hFk N).
Qed.

(** Source for [radon_agreement]: a Borel regular measure phi that
    agrees on open sets with a Radon measure rho equals rho, on a
    Hausdorff space covered by an increasing sequence of open sets with
    compact closures; supporting the Radon property of theta_n x L^{n-m}
    presupposed in Federer 2.7.16, p. 141, with 2.2.3 and 2.2.5,
    pp. 61–63. Supporting theorem; no metric is used. *)
Theorem radon_agreement : phi = rho.
Proof.
apply: funext=> S; apply/eqP; rewrite eq_le radon_agreement_upper andTb.
have [B [hSB [hB he]]] := borel_regular_cover hpr S.
rewrite he; apply: le_trans (measure_mono hrho hSB) _.
exact: radon_agreement_borel.
Qed.

End RadonComparison.

Section CompactProductRadon.
Variable R : realType.
Variables X Y : topologicalType.
Variables (alpha : set X -> \bar R) (beta : set Y -> \bar R).
Hypotheses (ha : is_measure alpha) (hb : is_measure beta).
Variables (A : (X -> R) -> R) (B : (Y -> R) -> R).
Variables (U : nat -> set X) (V : nat -> set Y) (W : nat -> set Y).
Hypotheses (hX : hausdorff_space X) (hXc : compact [set: X]).
Hypotheses (hY : hausdorff_space Y) (hYl : locally_compact [set: Y]).
Hypotheses (hU : is_countable_open_base U) (hV : is_countable_open_base V).
Hypotheses (hWo : forall k, open (W k)) (hWc : forall k, exists2 C, compact C & W k `<=` C)
  (hWinc : forall i j, (i <= j)%N -> W i `<=` W j) (hWY : forall y, exists k, W k y).
Hypotheses (hra : is_borel_regular_measure alpha) (hrb : is_borel_regular_measure beta).
Hypotheses (hAm : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
  (hBm : is_monotone_daniell_integral (@compactly_supported_continuous_functions R Y) B).
Hypotheses (hAr : is_real_integral_functional alpha (@compactly_supported_continuous_functions R X) A)
  (hBr : is_real_integral_functional beta (@compactly_supported_continuous_functions R Y) B).
Local Notation KXY := (@compactly_supported_continuous_functions R (X * Y)%type).

(** Source for [compact_product_iterated_daniell_product]: the iterated
    integral h |-> B_y[A_x h(x, y)] is the product of A and B in the
    sense of Federer 2.6.4, p. 119. Supporting lemma. *)
Lemma compact_product_iterated_daniell_product :
  is_daniell_product A B (fun h : X * Y -> R => B (fun y => A (fun x => h (x, y)))).
Proof.
have hXl := compact_space_locally_compact hXc.
have hAd := monotone_daniell_is_daniell hAm; have hBd := monotone_daniell_is_daniell hBm.
split; first exact: (@iterated_compact_functional_daniell R X Y A B hX hXl hY hYl hAd hBd).
move=> f g hf hg; exact: (@iterated_compact_functional_generator R X Y A B f g hAd hBd hf hg).
Qed.

(** Source for [compact_product_measure_represents]: alpha x beta
    represents the iterated integral on K(X x Y), Federer 2.6.4,
    p. 119, as corrected in the erratum, p. 2, book p. 119 line 19,
    used for "theta_n x L^{n-m}" in 2.7.16, p. 141. Supporting lemma. *)
Lemma compact_product_measure_represents :
  is_real_integral_functional (product_measure ha hb) KXY (fun h => B (fun y => A (fun x => h (x, y)))).
Proof.
have hXl := compact_space_locally_compact hXc.
move=> h hh.
exact: (daniell_product_measure_representation ha hb hX hXl hY hYl hAr hBr
  compact_product_iterated_daniell_product hh).
Qed.

(** Source for [compact_product_measure_radon]: the cartesian product
    alpha x beta (2.6.1, p. 114) is a Radon measure over X x Y,
    presupposed in "gamma = xi_#(theta_n x L^{n-m}) is a Radon measure
    over X", Federer 2.7.16, p. 141. Supporting theorem; see the header
    for the proof. *)
Theorem compact_product_measure_radon : is_radon_measure (product_measure ha hb).
Proof.
have hXl := compact_space_locally_compact hXc.
have hZH : hausdorff_space (X * Y)%type := product_hausdorff hX hY.
have hZl : locally_compact [set: (X * Y)%type] := product_locally_compact hXl hYl.
have hCm := daniell_product_is_monotone hX hXl hY hYl hAm hBm compact_product_iterated_daniell_product.
have [rho [hrm [hrr hrrep]]] := compact_support_radon_representation hZH hZl hCm.
have hUV := ProductCountableBase.laws hU hV.
pose WZ k : set (X * Y) := [set: X] `*` W k.
have hWZo k : open (WZ k).
  have -> : WZ k = (@snd X Y) @^-1` W k by apply/seteqP; split=> p //= [].
  by apply: open_comp (hWo k)=> p _; exact: second_projection_continuous.
have hWZc k : exists2 C, compact C & WZ k `<=` C.
  have [C hC hWC] := hWc k; exists ([set: X] `*` C); first exact: compact_setX.
  by move=> p [_ hp]; split=> //; exact: hWC.
have hWZinc i j : (i <= j)%N -> WZ i `<=` WZ j by move=> hij p [_ hp]; split=> //; apply: (hWinc hij); exact: hp.
have hWZT p : exists k, WZ k p by have [k hk] := hWY p.2; exists k.
have hpr : is_borel_regular_measure (product_measure ha hb).
  exact: (product_measure_borel_regular ha hb hU hV hra hrb).
have hL := @compactly_supported_continuous_functions_lattice R (X * Y)%type.
have hopen Z : open Z -> product_measure ha hb Z = rho Z.
  move=> hZ; have hlev := @compact_support_open_is_increasing_level R (X * Y)%type _ hZH hZl hUV Z hZ.
  rewrite -[rho Z]mul1e.
  exact: (represented_scaled_increasing_level hL (product_measure_is_measure ha hb) hrm
    compact_product_measure_represents hrrep (@ltr01 R) (fun f _ => esym (mul1r _)) hlev).
have -> : product_measure ha hb = rho.
  exact: (radon_agreement (product_measure_is_measure ha hb) hrm hZH hrr hpr hWZo hWZc hWZinc hWZT hopen).
exact: hrr.
Qed.

End CompactProductRadon.
