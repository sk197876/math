(** Federer (1969), 2.7.13, printed pp. 130–131: "Finally, to prove that
    beta^x is an epimorphism, it will suffice to show that the
    characteristic function of every gamma measurable set with compact
    closure belongs to T(Phi). Assuming that C is a compact subset of X, we
    use 2.7.10(5) to obtain f in K(G)+ with C subset A^x{g: f(g) > 0}. ...
    v_h = mu^x(u_h) with u_h = ([v_h / mu^x(f)] o A^x) . f in K(G)+, ...
    integral u_h d alpha = integral v_h d gamma ..." This module proves the
    surjectivity by a different route. By 2.7.10(5) every v in K(X)+ is
    mu^x(u) for the function u = ([v / mu^x(f)] o A^x) . f of K(G)+, whose
    alpha integral is nu(mu^x(u)) = integral v d gamma; thus mu^x has lifts
    which preserve the L_1 seminorm on K(X)+. Since gamma is K(X) regular,
    K(X)+ is dense in the nonnegative part of L_1(gamma) (2.5.3, p. 94, the
    second further condition; proof p. 95). For a nonnegative gamma summable
    v choose k_n in K(X)+ with integral |k_n - v| d gamma < 1/(n+1) -
    1/(n+2), lift the positive and negative parts of k_{n+1} - k_n, and sum
    the lifts by Lebesgue's increasing convergence theorem (2.4.7, p. 84) in
    L_1(alpha). Since beta^x does not increase the L_1 seminorm
    (coset_lone_integral_contraction) and extends mu^x, the sum u satisfies
    integral |beta^x(u) - v| d gamma = 0. The general case follows from v =
    (|v| + v)/2 - (|v| - v)/2. Federer's route through the characteristic
    functions of the subsets of C in F_j[K(X)] is not followed. The local
    erratum has no entry for pp. 130–131. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality functions
  reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialExtendedOrderLoci MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence ExtendedRealOrderLimit ExtendedRealReciprocalBounds
  RealLatticeTruncationLimits SummableRealFunctionUP SummableRealArithmetic LatticeL1ApproximationLaws
  TotalAbsoluteDifferenceGraph TotalScalarLpUP TotalLoneSummability FunctionLatticeUP FunctionLatticeLaws
  FunctionLatticeRegularityUP RegularDaniellEnvelope DaniellPositiveL1Density MonotoneDaniellIntegralUP
  RealIntegralFunctionalUP CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportProducts
  DaniellSpaceCompactness TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws HaarIntegralUP
  IsotropyGroupTopology CosetIntegralUP CosetIntegralLaws SummableIncreasingLimits CosetLoneIntegralUP
  CosetLoneIntegralLaws CosetLoneClass CosetLoneIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FiniteSums.
Variable R : realType.
Variable T : choiceType.
Variable phi : set T -> \bar R.
Hypothesis hphi : is_measure phi.

(** Source for [telescoping_real_sum]: sum_{n < N} (w_n - w_{n+1}) =
    w_0 - w_N, the elementary identity behind the choice of the
    errors 1/(n+1) - 1/(n+2) in the surjectivity proof of Federer
    2.7.13, p. 131. Supporting lemma. *)
Lemma telescoping_real_sum (w : nat -> R) N : \sum_(n < N) (w n - w n.+1) = w 0%N - w N.
Proof.
elim: N=> [|N ih]; first by rewrite big_ord0 subrr.
by rewrite big_ord_recr /= ih addrA subrK.
Qed.

(** Source for [finite_sum_integral]: the integral of a finite sum of
    summable functions is the sum of their integrals, Federer 2.4.4(4),
    p. 82; supporting 2.7.13, p. 131. Supporting lemma. *)
Lemma finite_sum_integral (f : nat -> T -> R) (c : nat -> R) N :
  (forall n, is_measure_integral phi (real_total_integrand (f n)) (c n)%:E) ->
  is_measure_integral phi (real_total_integrand (fun t => \sum_(n < N) f n t)) (\sum_(n < N) c n)%:E.
Proof.
move=> hf; elim: N=> [|N ih].
  have -> : (fun t => \sum_(n < 0) f n t) = (fun _ => 0) by apply: funext=> t; rewrite big_ord0.
  by rewrite big_ord0; exact: real_total_zero_integral hphi.
have -> : (fun t => \sum_(n < N.+1) f n t) = (fun t => \sum_(n < N) f n t + f N t).
  by apply: funext=> t; rewrite big_ord_recr.
by rewrite big_ord_recr /=; have h := real_total_integral_add hphi ih (hf N); exact: h.
Qed.

End FiniteSums.

Section CosetLoneIntegralOnto.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hX : hausdorff_space X.
Local Notation S := (isotropy_subgroup A x).
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hR : is_subgroup_restriction mul inv e S mulS invS eS.
Variable mu : (S -> R) -> R.
Hypothesis hmu : is_left_haar_integral mulS mu.
Variable M : (G -> R) -> X -> R.
Hypothesis hM : is_coset_integral mul A x mu M.
Variable nu : (X -> R) -> R.
Variables (alpha : set G -> \bar R) (beta : set S -> \bar R) (gamma : set X -> \bar R).
Hypotheses (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma).
Hypothesis harep : is_real_integral_functional alpha KG (fun u => nu (M u)).
Hypothesis hbrep : is_real_integral_functional beta KS mu.
Hypothesis hcrep : is_real_integral_functional gamma KX nu.
Hypothesis hcreg : is_function_lattice_regular KX gamma.
Variable B : (G -> R) -> X -> R.
Hypothesis hB : is_coset_lone_integral mul A x alpha beta gamma B.

(** Source for [hLG]: the lattice laws of K(G), Federer 2.5.13,
    p. 106, used in this section. *)
Let hLG : is_function_lattice KG := @compactly_supported_continuous_functions_lattice R G.
(** Source for [hLX]: the lattice laws of K(X), Federer 2.5.13,
    p. 106, used in this section. *)
Let hLX : is_function_lattice KX := @compactly_supported_continuous_functions_lattice R X.

(** Source for [coset_integral_positive_lift]: "v_h = mu^x(u_h) with
    u_h = ([v_h / mu^x(f)] o A^x) . f in K(G)+", Federer 2.7.13, proof,
    p. 131, from 2.7.10(5), p. 127: every v in K(X)+ is mu^x(u) for
    some u in K(G)+, and then integral u d alpha = nu(mu^x(u)) =
    integral v d gamma. Supporting lemma. *)
Lemma coset_integral_positive_lift v : positive_function_lattice KX v ->
  exists u, [/\ positive_function_lattice KG u, M u = v &
    is_measure_integral alpha (real_total_integrand u) (nu v)%:E].
Proof.
move=> [hv hv0].
have [f hf hsub] := coset_integral_cover x hG hA hv.
have [_ [hqc _]] := coset_integral_quotient_compact hG hA hX hR hmu hM hv hf hsub.
have [hfK hf0] := hf.
have hMf0 := coset_integral_nonnegative hG hA hX hmu hM hfK hf0.
have hMu := coset_integral_quotient hG hA hX hR hmu hM hv hf hsub.
have hu : KG (fun g => v (A g x) / M f (A g x) * f g).
  apply: compact_support_continuous_multiplier hfK=> g.
  apply: (@continuous_comp G X (real_line_metric R) (orbit_map A x) (fun y => v y / M f y) g).
    exact: orbit_map_continuous hA x g.
  exact: hqc.
exists (fun g => v (A g x) / M f (A g x) * f g); split=> //.
- split=> // g; apply: mulr_ge0 (hf0 g); apply: divr_ge0; [exact: hv0|exact: hMf0].
- by have h := harep hu; rewrite /= hMu in h.
Qed.

(** Source for [regular_compact_density]: "For each nonnegative phi
    summable function u, and each delta > 0, there exists a function
    k in L+ such that integral |k - u| d phi < 4 delta", Federer 2.5.3,
    p. 94, for the K(X) regular measure gamma, in the arbitrary
    epsilon form of daniell_nonnegative_summable_lattice_density;
    supporting the surjectivity in 2.7.13, p. 131. Supporting lemma. *)
Lemma regular_compact_density (v : X -> R) (d : R) : summable_real_functions gamma v ->
  (forall y, 0 <= v y) -> 0 < d ->
  exists k (q : R), [/\ positive_function_lattice KX k,
    is_measure_integral gamma (real_total_integrand (fun y => `|k y - v y|)) q%:E & q < d].
Proof.
move=> hs hv0 hd.
have hp : measure_almost_everywhere gamma (partial_extended_nonnegative_locus (real_total_integrand v)).
  apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_true hc))=> y _.
  by exists (v y)%:E; split; [exact/real_total_integrand_graph|rewrite lee_fin].
have henv := regular_representing_measure_envelope hLX hc hcrep hcreg.
have [k [q [hk [hi hq]]]] := daniell_nonnegative_summable_lattice_density hLX hc hcrep henv hs hp hd.
exists k, q; split=> //.
exact: (measure_integral_graph_equivalent (total_absolute_difference_graph k v) hi).
Qed.

(** Source for [coset_lone_integral_onto_nonnegative]: "to prove that
    beta^x is an epimorphism", Federer 2.7.13, proof, p. 131, for a
    nonnegative gamma summable function v: some alpha summable u
    satisfies beta^x(u) = v gamma almost everywhere. Different proof
    route, described in the header of this module. *)
Theorem coset_lone_integral_onto_nonnegative v : summable_real_functions gamma v -> (forall y, 0 <= v y) ->
  exists2 u, summable_real_functions alpha u & measure_almost_everywhere gamma [set y | B u y = v y].
Proof.
move=> hv hv0.
pose w n : R := ((n.+1)%:R)^-1.
pose eps n := w n - w n.+1.
have hw0 n : 0 < w n by rewrite /w invr_gt0 ltr0n.
have heps n : 0 < eps n.
  by rewrite /eps subr_gt0 /w ltf_pV2 ?posrE ?ltr0n // ltr_nat.
have hepsw n : eps n <= w n by rewrite /eps lerBlDr lerDl; exact: ltW (hw0 n.+1).
have /choice [kq hkq] : forall n, exists kq : (X -> R) * R,
    [/\ positive_function_lattice KX kq.1,
      is_measure_integral gamma (real_total_integrand (fun y => `|kq.1 y - v y|)) kq.2%:E & kq.2 < eps n].
  by move=> n; have [k [q h]] := regular_compact_density hv hv0 (heps n); exists (k, q).
pose k n := (kq n).1.
pose q n := (kq n).2.
have hk n : positive_function_lattice KX (k n) by case: (hkq n).
have hki n : is_measure_integral gamma (real_total_integrand (fun y => `|k n y - v y|)) (q n)%:E.
  by case: (hkq n).
have hq n : q n < eps n by case: (hkq n).
pose dd n y := k n.+1 y - k n y.
have hdd n : KX (dd n).
  have h := function_lattice_add hLX (hk n.+1).1 (compactly_supported_scale (-1) (hk n).1).
  have -> : dd n = (fun y => k n.+1 y + -1 * k n y) by apply: funext=> y; rewrite mulN1r.
  exact: h.
pose dp n y := Order.max (dd n y) 0.
pose dm n y := Order.max (- dd n y) 0.
have hdp n : positive_function_lattice KX (dp n).
  split; last by move=> y; rewrite le_max lexx orbT.
  have h := function_lattice_positive_part hLX (hdd n); exact: h.
have hdm n : positive_function_lattice KX (dm n).
  split; last by move=> y; rewrite le_max lexx orbT.
  have h := function_lattice_negative_part hLX (hdd n); exact: h.
have hdpm n y : dp n y - dm n y = dd n y.
  rewrite /dp /dm; move: (dd n y)=> a; rewrite !maxEle.
  by case: (lerP a 0)=> h1; case: (lerP (- a) 0)=> h2 /=; lra.
have hdpm' n y : dp n y + dm n y = `|dd n y|.
  rewrite /dp /dm; move: (dd n y)=> a; rewrite !maxEle.
  case: (lerP a 0)=> h1; case: (lerP (- a) 0)=> h2 /=.
  - have ha0 : a = 0 by lra.
    by rewrite ha0 normr0 addr0.
  - by rewrite add0r ler0_norm.
  - by rewrite addr0 gtr0_norm.
  - lra.
have hnu n : nu (dp n) + nu (dm n) <= q n.+1 + q n.
  have hpt y : dp n y + dm n y <= `|k n.+1 y - v y| + `|k n y - v y|.
    rewrite hdpm' /dd.
    have -> : k n.+1 y - k n y = (k n.+1 y - v y) - (k n y - v y) by rewrite opprB addrA subrK.
    exact: ler_normB.
  have h1 := real_total_integral_add hc (hcrep (hdp n).1) (hcrep (hdm n).1).
  have h2 := real_total_integral_add hc (hki n.+1) (hki n).
  have h := summable_total_integral_le_almost hc h1 h2
    (measure_almost_everywhere_mono hc (fun y _ => hpt y) (measure_almost_everywhere_true hc)).
  by rewrite lee_fin in h.
have hnu0 (f : X -> R) : positive_function_lattice KX f -> 0 <= nu f.
  move=> [hf hf0]; have h := summable_total_integral_le_almost hc (real_total_zero_integral hc) (hcrep hf)
    (measure_almost_everywhere_mono hc (fun y _ => hf0 y) (measure_almost_everywhere_true hc)).
  by rewrite lee_fin in h.
have /choice [ep hep] : forall n, exists u, [/\ positive_function_lattice KG u, M u = dp n &
    is_measure_integral alpha (real_total_integrand u) (nu (dp n))%:E].
  by move=> n; exact: coset_integral_positive_lift (hdp n).
have /choice [em hem] : forall n, exists u, [/\ positive_function_lattice KG u, M u = dm n &
    is_measure_integral alpha (real_total_integrand u) (nu (dm n))%:E].
  by move=> n; exact: coset_integral_positive_lift (hdm n).
have [l0 [hl0 hMl0 hl0i]] := coset_integral_positive_lift (hk 0%N).
pose Up N g := \sum_(n < N) ep n g.
pose Um N g := \sum_(n < N) em n g.
have hepK n : KG (ep n) by case: (hep n)=> -[].
have hemK n : KG (em n) by case: (hem n)=> -[].
have hep0 n g : 0 <= ep n g by case: (hep n)=> -[_ h] _ _; exact: h.
have hem0 n g : 0 <= em n g by case: (hem n)=> -[_ h] _ _; exact: h.
have hepM n : M (ep n) = dp n by case: (hep n).
have hemM n : M (em n) = dm n by case: (hem n).
have hepi n : is_measure_integral alpha (real_total_integrand (ep n)) (nu (dp n))%:E by case: (hep n).
have hemi n : is_measure_integral alpha (real_total_integrand (em n)) (nu (dm n))%:E by case: (hem n).
have hUpi N : is_measure_integral alpha (real_total_integrand (Up N)) (\sum_(n < N) nu (dp n))%:E.
  have h := @finite_sum_integral R G alpha ha ep (fun n => nu (dp n)) N hepi; exact: h.
have hUmi N : is_measure_integral alpha (real_total_integrand (Um N)) (\sum_(n < N) nu (dm n))%:E.
  have h := @finite_sum_integral R G alpha ha em (fun n => nu (dm n)) N hemi; exact: h.
have hsum N : \sum_(n < N) (q n.+1 + q n) <= 2.
  apply: (@le_trans _ _ (\sum_(n < N) (eps n.+1 + eps n))).
    by apply: ler_sum=> n _; apply: lerD; exact: ltW (hq _).
  rewrite big_split /= /eps (telescoping_real_sum (fun n => w n.+1)) telescoping_real_sum.
  have hw1 n : w n <= 1 by rewrite /w invf_le1 ?ltr0n // ler1n.
  have h1 : w 1%N - w N.+1 <= 1.
    apply: le_trans (hw1 1%N); rewrite lerBlDr lerDl; exact: ltW (hw0 _).
  have h0 : w 0%N - w N <= 1.
    apply: le_trans (hw1 0%N); rewrite lerBlDr lerDl; exact: ltW (hw0 _).
  by apply: (le_trans (lerD h1 h0)); rewrite -mulr2n.
have hUpb N : \sum_(n < N) nu (dp n) <= 2.
  apply: le_trans (hsum N); apply: ler_sum=> n _; apply: le_trans (hnu n).
  by rewrite lerDl; exact: hnu0 (hdm n).
have hUmb N : \sum_(n < N) nu (dm n) <= 2.
  apply: le_trans (hsum N); apply: ler_sum=> n _; apply: le_trans (hnu n).
  by rewrite lerDr; exact: hnu0 (hdp n).
have hUpmon N : measure_almost_everywhere alpha [set g | Up N g <= Up N.+1 g].
  apply: (measure_almost_everywhere_mono ha _ (measure_almost_everywhere_true ha))=> g _.
  by rewrite /= /Up big_ord_recr /= lerDl.
have hUmmon N : measure_almost_everywhere alpha [set g | Um N g <= Um N.+1 g].
  apply: (measure_almost_everywhere_mono ha _ (measure_almost_everywhere_true ha))=> g _.
  by rewrite /= /Um big_ord_recr /= lerDl.
have [Pp [cp [hPpi hcp hPpc]]] := summable_almost_increasing_limit ha hUpi hUpmon hUpb.
have [Pm [cm [hPmi hcm hPmc]]] := summable_almost_increasing_limit ha hUmi hUmmon hUmb.
pose u g := l0 g + Pp g - Pm g.
have hus : summable_real_functions alpha u.
  have h1 : summable_real_functions alpha l0 by exists (nu (k 0%N)).
  have h2 : summable_real_functions alpha Pp by exists cp.
  have h3 : summable_real_functions alpha Pm by exists cm.
  have h := summable_real_subtract ha (summable_real_add ha h1 h2) h3; exact: h.
pose Sn N g := l0 g + (Up N g - Um N g).
have hSK N : KG (Sn N).
  have hUK (f : nat -> G -> R) : (forall n, KG (f n)) -> forall N, KG (fun g => \sum_(n < N) f n g).
    move=> hf; elim=> [|N' ih].
      have -> : (fun g => \sum_(n < 0) f n g) = (fun _ => 0) by apply: funext=> g; rewrite big_ord0.
      have h := function_lattice_zero hLG hl0.1; exact: h.
    have -> : (fun g => \sum_(n < N'.+1) f n g) = (fun g => \sum_(n < N') f n g + f N' g).
      by apply: funext=> g; rewrite big_ord_recr.
    have h := function_lattice_add hLG ih (hf N'); exact: h.
  have hp := hUK ep hepK N.
  have hm := hUK em hemK N.
  have h := function_lattice_add hLG hl0.1 (function_lattice_add hLG hp (compactly_supported_scale (-1) hm)).
  have -> : Sn N = (fun g => l0 g + (Up N g + -1 * Um N g)) by apply: funext=> g; rewrite mulN1r.
  exact: h.
have hMS N : M (Sn N) = k N.
  elim: N=> [|N ih].
    have -> : Sn 0%N = l0 by apply: funext=> g; rewrite /Sn /Up /Um !big_ord0 subrr addr0.
    exact: hMl0.
  have hpN := hepK N.
  have hmN := hemK N.
  have he : Sn N.+1 = (fun g => (Sn N g + ep N g) + -1 * em N g).
    apply: funext=> g; rewrite /Sn /Up /Um !big_ord_recr /= mulN1r.
    by rewrite opprD addrACA !addrA.
  have hSp := function_lattice_add hLG (hSK N) hpN.
  rewrite he (coset_integral_add hG hA hX hmu hM hSp (compactly_supported_scale (-1) hmN)).
  rewrite (coset_integral_scale hG hA hX hmu hM (-1) hmN) (coset_integral_add hG hA hX hmu hM (hSK N) hpN).
  rewrite ih hepM hemM.
  apply: funext=> y; rewrite mulN1r -addrA hdpm /dd addrC subrK.
  by [].
pose D y := `|B u y - v y|.
have hBu := coset_lone_integral_summable hB hus.
have [cD hcD] : summable_real_functions gamma D.
  have h := summable_real_absolute hc (summable_real_subtract hc hBu hv); exact: h.
have hD0 : measure_almost_everywhere gamma [set y | 0 <= D y].
  apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_true hc))=> y _.
  exact: normr_ge0.
have hbound N : cD <= (cp - \sum_(n < N) nu (dp n)) + (cm - \sum_(n < N) nu (dm n)) + q N.
  pose r g := u g - Sn N g.
  have hrS : summable_real_functions alpha (Sn N) by exists (nu (M (Sn N))); exact: harep (hSK N).
  have hr : summable_real_functions alpha r by have h := summable_real_subtract ha hus hrS; exact: h.
  have [t ht] : summable_real_functions alpha (fun g => `|r g|).
    have h := summable_real_absolute ha hr; exact: h.
  have htle : t <= (cp - \sum_(n < N) nu (dp n)) + (cm - \sum_(n < N) nu (dm n)).
    have h1 := real_total_integral_subtract ha hPpi (hUpi N).
    have h2 := real_total_integral_subtract ha hPmi (hUmi N).
    have h3 := real_total_integral_add ha h1 h2.
    have hae : measure_almost_everywhere alpha
        [set g | `|r g| <= (Pp g - Up N g) + (Pm g - Um N g)].
      apply: (measure_almost_everywhere_mono ha _ (measure_almost_everywhere_and ha hPpc hPmc)).
      move=> g /= [hgp hgm].
      have hp' := extended_increases_to_upper hgp N; have hm' := extended_increases_to_upper hgm N.
      rewrite lee_fin in hp'; rewrite lee_fin in hm'.
      have -> : r g = (Pp g - Up N g) - (Pm g - Um N g) by rewrite /r /u /Sn; lra.
      apply: le_trans (ler_normB _ _) _.
      by rewrite !ger0_norm // subr_ge0.
    have h := summable_total_integral_le_almost ha ht h3 hae.
    by rewrite lee_fin in h.
  have hBr := coset_lone_integral_identity hB ht.
  have hsplit := coset_lone_integral_add hA ha hb hc hB hrS hr.
  have hext := coset_lone_integral_extends hG hA hX hM hc harep hbrep hB (hSK N).
  have habs := coset_lone_integral_absolute hA ha hb hc hB hr.
  have hRi := real_total_integral_add hc (hki N) hBr.
  have hae : measure_almost_everywhere gamma [set y | D y <= `|k N y - v y| + B (fun g => `|r g|) y].
    apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc hsplit
      (measure_almost_everywhere_and hc hext habs))).
    move=> y /= [hy1 [hy2 hy3]].
    have hu' : (fun g => Sn N g + r g) = u by apply: funext=> g; rewrite /r addrC subrK.
    rewrite hu' in hy1; rewrite /D hy1 hy2 hMS.
    have -> : k N y + B r y - v y = (k N y - v y) + B r y by rewrite addrAC.
    apply: le_trans (ler_normD _ _) _; exact: lerD (lexx _) hy3.
  have h := summable_total_integral_le_almost hc hcD hRi hae.
  rewrite lee_fin in h; apply: le_trans h _; rewrite addrC lerD2r; exact: htle.
have hcD0 : cD <= 0.
  apply/ler_addgt0Pr=> eta heta; rewrite add0r.
  have heta3 : 0 < eta / 3%:R by rewrite divr_gt0 // ltr0n.
  have hlt1 : ((cp - eta / 3%:R)%:E < cp%:E)%E by rewrite lte_fin ltrBlDr ltrDl.
  have hlt2 : ((cm - eta / 3%:R)%:E < cm%:E)%E by rewrite lte_fin ltrBlDr ltrDl.
  have [N1 hN1] := hcp.2.1 _ hlt1.
  have [N2 hN2] := hcm.2.1 _ hlt2.
  have [N3 hN3] := positive_reciprocal_nat_small heta3.
  pose N := maxn N1 (maxn N2 N3).
  have h1 := hN1 N (leq_maxl _ _); rewrite lte_fin ltrBlDr -ltrBlDl in h1.
  have h2 := hN2 N (leq_trans (leq_maxl N2 N3) (leq_maxr _ _)); rewrite lte_fin ltrBlDr -ltrBlDl in h2.
  have h3 : q N < eta / 3%:R.
    apply: lt_le_trans (hq N) _; apply: le_trans (hepsw N) _; apply: ltW; apply: le_lt_trans hN3.
    exact: positive_reciprocal_nat_antitone (leq_trans (leq_maxr N2 N3) (leq_maxr _ _)).
  apply: le_trans (hbound N) _; apply: ltW.
  have -> : eta = eta / 3%:R + eta / 3%:R + eta / 3%:R by lra.
  exact: ltrD (ltrD h1 h2) h3.
have hcDe : cD = 0.
  apply/eqP; rewrite eq_le hcD0 /=.
  have h := summable_total_integral_le_almost hc (real_total_zero_integral hc) hcD hD0.
  by rewrite lee_fin in h.
rewrite hcDe in hcD.
have hz := summable_total_nonnegative_zero_almost hc hcD hD0.
exists u=> //; apply: (measure_almost_everywhere_mono hc _ hz)=> y /= hy.
by apply/eqP; rewrite -subr_eq0 -normr_eq0; apply/eqP.
Qed.

(** Source for [coset_lone_integral_onto]: "beta^x is an epimorphism",
    Federer 2.7.13, pp. 130–131: every gamma summable v is gamma almost
    equal to beta^x(u) for some alpha summable u. The general case
    follows from the nonnegative one by v = (|v| + v)/2 - (|v| - v)/2
    and the linearity of beta^x. Direct formalisation. *)
Theorem coset_lone_integral_onto v : summable_real_functions gamma v ->
  exists2 u, summable_real_functions alpha u & measure_almost_everywhere gamma [set y | B u y = v y].
Proof.
move=> hv; have hav := summable_real_absolute hc hv.
have hp : summable_real_functions gamma (fun y => `|v y| + v y).
  have h := summable_real_add hc hav hv; exact: h.
have hq : summable_real_functions gamma (fun y => `|v y| - v y).
  have h := summable_real_subtract hc hav hv; exact: h.
have hp0 y : 0 <= `|v y| + v y.
  by rewrite -lerBlDr sub0r; have := ler_norm (- v y); rewrite normrN.
have hq0 y : 0 <= `|v y| - v y by rewrite subr_ge0; exact: ler_norm.
have [up hup hBp] := coset_lone_integral_onto_nonnegative hp hp0.
have [uq huq hBq] := coset_lone_integral_onto_nonnegative hq hq0.
have hd := summable_real_subtract ha hup huq.
exists (fun g => 2^-1 * (up g - uq g)); first by have h := summable_real_scale ha (2^-1) hd; exact: h.
have hl1 := coset_lone_integral_scale hA ha hb hc hB (2^-1) hd.
have hl2 := coset_lone_integral_add hA ha hb hc hB hup (summable_real_scale ha (-1) huq).
have hl3 := coset_lone_integral_scale hA ha hb hc hB (-1) huq.
have h5 := measure_almost_everywhere_and hc hl1 (measure_almost_everywhere_and hc hl2
  (measure_almost_everywhere_and hc hl3 (measure_almost_everywhere_and hc hBp hBq))).
apply: (measure_almost_everywhere_mono hc _ h5)=> y /= [h1 [h2 [h3 [h4 h5']]]].
have he : (fun g => up g - uq g) = (fun g => up g + -1 * uq g) by apply: funext=> g; rewrite mulN1r.
rewrite h1 he h2 h3 h4 h5' mulN1r.
by rewrite opprB addrC addrA subrK mulrDr [2^-1 * _]mulrC -splitr.
Qed.

End CosetLoneIntegralOnto.
