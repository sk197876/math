(** Federer (1969), 2.5.17, p. 111: defining the linear function mu : K(R)
    -> R so that mu(f) = int_a^b f dg whenever f in K(R) and spt f is
    contained in {x : a <= x <= b}, one sees from 2.5.13 that mu is a
    Daniell integral. The value is taken over a symmetric segment containing
    the support, and its independence of the segment follows from the
    additivity of the integral and the vanishing of the sums where f
    vanishes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength FunctionLatticeUP
  LatticeAdditiveFunctional FunctionLatticeSeminormUP DaniellIntegralUP CompactSupportFunctionUP
  CompactSupportFunctionLattice CompactSupportRieszRepresentation CompactMaximum StieltjesSums
  StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InducedDaniell.
Variable R : realType.
Variable g : R -> R.
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
Local Notation KR := (@compactly_supported_continuous_functions R R).

(** Source for [compact_real_bounded]: supporting boundedness of a
    compact subset of the real line, Federer 2.5.17, p. 111. *)
Lemma compact_real_bounded (A : set R) : compact A -> exists M, forall x, A x -> `|x| <= M.
Proof.
move=> h; have hb : compact (A : set R^o) := h.
have hbd := compact_bounded hb.
have [M hM] := @filter_ex _ _ proper_pinfty_nbhs _ hbd.
by exists M=> x hx; exact: hM.
Qed.

(** Source for [stieltjes_sum_zero_mem]: a Riemann-Stieltjes sum
    vanishes when f vanishes at all terms, Federer 2.5.17, p. 111. *)
Lemma stieltjes_sum_zero_mem (f : R -> R) (a b : R) (w : seq R) :
  (forall x, x \in w -> a <= x <= b) -> (forall x, a <= x <= b -> f x = 0) ->
  stieltjes_sum f g w = 0.
Proof.
have [n] := ubnP (size w); elim: n w=> // n ih [|t [|u [|t' rest]]] hsize hb hf //.
rewrite stieltjes_sum_cons (hf u) ?mul0r ?add0r; last by apply: hb; rewrite !inE eqxx orbT.
apply: ih=> //; first by move: hsize; rewrite /= ltnS; exact: ltnW.
by move=> x hx; apply: hb; rewrite 2!in_cons hx !orbT.
Qed.

(** Source for [stieltjes_integral_zero]: int_a^b f dg = 0 when f
    vanishes on [a, b], Federer 2.5.17, p. 111. *)
Lemma stieltjes_integral_zero (f : R -> R) (a b : R) :
  continuous f -> a <= b -> (forall x, a <= x <= b -> f x = 0) -> stieltjes_integral g f a b = 0.
Proof.
move=> hf hab hz; symmetry; apply: (stieltjes_integral_unique hg hf hab)=> e he.
exists 1; split=> // w hw _.
rewrite (stieltjes_sum_zero_mem _ hz) ?subrr ?normr0 // => x hx.
have := sorted_mem_bounds hw.1 hx.
by rewrite (tagged_partition_head0 hw) (tagged_partition_last0 hw).
Qed.

(** Source for [support_radius]: a radius beyond which f vanishes,
    chosen from the compact support in Federer 2.5.17, p. 111. *)
Definition support_radius (f : R -> R) : R :=
  if pselect (exists N, 0 <= N /\ forall x, f x <> 0 -> `|x| <= N) is left h then sval (cid h) else 0.

(** Source for [support_radius_specP]: the chosen radius bounds the
    points where f does not vanish, Federer 2.5.17, p. 111. *)
Lemma support_radius_specP (f : R -> R) :
  (exists N, 0 <= N /\ forall x, f x <> 0 -> `|x| <= N) ->
  0 <= support_radius f /\ forall x, f x <> 0 -> `|x| <= support_radius f.
Proof.
move=> h; rewrite /support_radius; case: pselect=> [h'|hn]; last by case: hn.
exact: svalP (cid h').
Qed.

(** Source for [compact_support_bound]: a member of K(R) vanishes
    outside a bounded set, Federer 2.5.17, p. 111. *)
Lemma compact_support_bound (f : R -> R) :
  KR f -> exists N, 0 <= N /\ forall x, f x <> 0 -> `|x| <= N.
Proof.
move=> [_ hc]; have [M hM] := compact_real_bounded hc.
exists (Order.max M 0); split; first by rewrite le_max lexx orbT.
move=> x hx; rewrite le_max; apply/orP; left; apply: hM.
exact: subset_closure.
Qed.

(** Source for [KR_continuous]: a member of K(R) is continuous,
    Federer 2.5.13, p. 106, and 2.5.17, p. 111. *)
Lemma KR_continuous (f : R -> R) : KR f -> continuous f.
Proof. by move=> [hf _]; exact: hf. Qed.

(** Source for [induced_daniell]: the linear function mu of Federer
    2.5.17, p. 111, mu(f) = int_a^b f dg over a symmetric segment
    beyond which f vanishes. *)
Definition induced_daniell (f : R -> R) : R :=
  stieltjes_integral g f (- (support_radius f + 1)) (support_radius f + 1).

(** Source for [stieltjes_integral_symmetric_extend]: the integral over
    [-M, M] equals the integral over [-c, c] when f vanishes for
    |x| >= c, Federer 2.5.17, p. 111. *)
Lemma stieltjes_integral_symmetric_extend (f : R -> R) (c M : R) :
  continuous f -> 0 <= c -> c <= M -> (forall x, f x <> 0 -> `|x| < c) ->
  stieltjes_integral g f (- M) M = stieltjes_integral g f (- c) c.
Proof.
move=> hf hc0 hcM hz.
have hMc : - M <= - c by rewrite lerN2.
have hcc : - c <= c by lra.
have hMc' : - M <= c by lra.
have hzl : forall x, - M <= x <= - c -> f x = 0.
  move=> x /andP[_ hx]; case: (pselect (f x = 0))=> // hne.
  by have := hz x hne; rewrite ltr_norml=> /andP[h1 _]; lra.
have hzr : forall x, c <= x <= M -> f x = 0.
  move=> x /andP[hx _]; case: (pselect (f x = 0))=> // hne.
  by have := hz x hne; rewrite ltr_norml=> /andP[_ h2]; lra.
rewrite -(stieltjes_integral_cat hg hf hMc' hcM) -(stieltjes_integral_cat hg hf hMc hcc).
by rewrite (stieltjes_integral_zero hf hMc hzl) (stieltjes_integral_zero hf hcM hzr) add0r addr0.
Qed.

(** Source for [induced_daniell_eq]: mu(f) = int_{-N}^N f dg for every
    N beyond which f vanishes, the independence of the segment in
    Federer 2.5.17, p. 111. *)
Lemma induced_daniell_eq (f : R -> R) (N : R) :
  continuous f -> (exists N', 0 <= N' /\ forall x, f x <> 0 -> `|x| <= N') ->
  0 <= N -> (forall x, f x <> 0 -> `|x| < N) ->
  stieltjes_integral g f (- N) N = induced_daniell f.
Proof.
move=> hf hex hN0 hz; have [hr0 hr] := support_radius_specP hex.
pose M := Order.max N (support_radius f + 1).
have hNM : N <= M by rewrite /M le_max lexx.
have hrM : support_radius f + 1 <= M by rewrite /M le_max lexx orbT.
have hr1 : 0 <= support_radius f + 1 by lra.
have hz' : forall x, f x <> 0 -> `|x| < support_radius f + 1.
  by move=> x hx; have := hr x hx; lra.
rewrite -(stieltjes_integral_symmetric_extend hf hN0 hNM hz) /induced_daniell.
by rewrite -(stieltjes_integral_symmetric_extend hf hr1 hrM hz').
Qed.

(** Source for [induced_daniell_value]: mu(f) = int_a^b f dg whenever
    f in K(R) vanishes outside the open interval {x : a < x < b},
    Federer 2.5.17, p. 111; for continuous f this is the condition
    spt f subset {x : a <= x <= b}. *)
Theorem induced_daniell_value (f : R -> R) (a b : R) :
  KR f -> a <= b -> (forall x, f x <> 0 -> a < x < b) ->
  induced_daniell f = stieltjes_integral g f a b.
Proof.
move=> hf hab hz; have hcont := KR_continuous hf.
have /andP[ha1 ha2] : - `|a| <= a <= `|a| by rewrite -ler_norml.
have /andP[hb1 hb2] : - `|b| <= b <= `|b| by rewrite -ler_norml.
have hna := normr_ge0 a; have hnb := normr_ge0 b.
pose N := `|a| + `|b| + 1.
have hN0 : 0 <= N by rewrite /N; lra.
have haN : - N <= a by rewrite /N; lra.
have hbN : b <= N by rewrite /N; lra.
have hzN : forall x, f x <> 0 -> `|x| < N.
  move=> x hx; have /andP[h1 h2] := hz x hx.
  by rewrite ltr_norml; apply/andP; split; rewrite /N; lra.
rewrite -(induced_daniell_eq hcont (compact_support_bound hf) hN0 hzN).
have hz1 : forall x, - N <= x <= a -> f x = 0.
  move=> x /andP[_ hxa]; case: (pselect (f x = 0))=> // hne.
  by have /andP[h1 _] := hz x hne; lra.
have hz2 : forall x, b <= x <= N -> f x = 0.
  move=> x /andP[hbx _]; case: (pselect (f x = 0))=> // hne.
  by have /andP[_ h2] := hz x hne; lra.
have haN' : - N <= b by lra.
rewrite -(stieltjes_integral_cat hg hcont haN' hbN) -(stieltjes_integral_cat hg hcont haN hab).
by rewrite (stieltjes_integral_zero hcont haN hz1) (stieltjes_integral_zero hcont hbN hz2) add0r addr0.
Qed.

(** Source for [induced_daniell_add]: mu is additive, the linearity of
    Federer 2.5.17, p. 111. *)
Lemma induced_daniell_add (f1 f2 : R -> R) :
  KR f1 -> KR f2 -> induced_daniell (fun x => f1 x + f2 x) = induced_daniell f1 + induced_daniell f2.
Proof.
move=> hf1 hf2.
have hf := function_lattice_add (@compactly_supported_continuous_functions_lattice R R) hf1 hf2.
have [N1 [hN1 hz1]] := compact_support_bound hf1.
have [N2 [hN2 hz2]] := compact_support_bound hf2.
pose N := N1 + N2 + 1.
have hN0 : 0 <= N by rewrite /N; lra.
have hzs1 : forall x, f1 x <> 0 -> `|x| < N by move=> x hx; have := hz1 x hx; rewrite /N; lra.
have hzs2 : forall x, f2 x <> 0 -> `|x| < N by move=> x hx; have := hz2 x hx; rewrite /N; lra.
have hzs : forall x, f1 x + f2 x <> 0 -> `|x| < N.
  move=> x hx; case: (pselect (f1 x = 0))=> [h1|h1]; last exact: hzs1.
  by apply: hzs2=> h2; apply: hx; rewrite h1 h2 addr0.
have hN : - N <= N by lra.
rewrite -(induced_daniell_eq (KR_continuous hf) (compact_support_bound hf) hN0 hzs).
rewrite -(induced_daniell_eq (KR_continuous hf1) (compact_support_bound hf1) hN0 hzs1).
rewrite -(induced_daniell_eq (KR_continuous hf2) (compact_support_bound hf2) hN0 hzs2).
exact (stieltjes_integral_add hg (KR_continuous hf1) (KR_continuous hf2) (KR_continuous hf) hN).
Qed.

(** Source for [continuous_scale]: supporting continuity of a scalar
    multiple of a continuous real function, Federer 2.5.17, p. 111. *)
Lemma continuous_scale (c : R) (f : R -> R) : continuous f -> continuous (fun x => c * f x).
Proof.
move=> hf y; apply/cvg_ballP=> e he.
have hc1 : 0 < `|c| + 1 by have := normr_ge0 c; lra.
have he' : 0 < e / (`|c| + 1) by rewrite divr_gt0.
have hb0 : nbhs y (f @^-1` ball (f y) (e / (`|c| + 1))).
  by exact ((cvg_ballP _ _).1 (hf y) _ he').
near=> x; rewrite /ball /= -mulrBr normrM.
have hx : `|f y - f x| < e / (`|c| + 1).
  by near: x; move: hb0; apply: filterS=> x' /=; rewrite /ball /=.
rewrite ltr_pdivlMr // in hx; apply: le_lt_trans _ hx; rewrite mulrC.
by apply: ler_wpM2l; [exact: normr_ge0 | rewrite lerDl ler01].
Unshelve. all: end_near.
Qed.

(** Source for [induced_daniell_scale]: mu is homogeneous, the linearity
    of Federer 2.5.17, p. 111. *)
Lemma induced_daniell_scale (c : R) (f : R -> R) :
  KR f -> induced_daniell (fun x => c * f x) = c * induced_daniell f.
Proof.
move=> hf; have hcont := KR_continuous hf; have hcf := continuous_scale (c := c) hcont.
have [N1 [hN1 hz1]] := compact_support_bound hf.
pose N := N1 + 1.
have hN0 : 0 <= N by rewrite /N; lra.
have hzs : forall x, f x <> 0 -> `|x| < N by move=> x hx; have := hz1 x hx; rewrite /N; lra.
have hzc : forall x, c * f x <> 0 -> `|x| < N.
  by move=> x hx; apply: hzs=> h0; apply: hx; rewrite h0 mulr0.
have hexc : exists N', 0 <= N' /\ forall x, c * f x <> 0 -> `|x| <= N'.
  by exists N1; split=> // x hx; apply: hz1=> h0; apply: hx; rewrite h0 mulr0.
have hN : - N <= N by lra.
rewrite -(induced_daniell_eq hcf hexc hN0 hzc).
rewrite -(induced_daniell_eq hcont (compact_support_bound hf) hN0 hzs).
exact (stieltjes_integral_scale hg hcont hcf hN).
Qed.

(** Source for [induced_daniell_order_bounded]: mu is bounded on the
    positive order intervals of K(R), the hypothesis of 2.5.13 verified
    in Federer 2.5.17, p. 111, by |int_{-N}^N k dg| <= sup u V_{-N}^N g. *)
Lemma induced_daniell_order_bounded (u : R -> R) : positive_function_lattice KR u ->
  exists b, forall k, lattice_positive_order_interval KR u k -> induced_daniell k <= b.
Proof.
move=> [hu hu0].
have [N1 [hN1 hz1]] := compact_support_bound hu.
pose N := N1 + 1.
have hN0 : 0 <= N by rewrite /N; lra.
have hN : - N <= N by lra.
have hcu : continuous (u : R -> R^o) := hu.1.
have hne : `[- N, N] !=set0 by exists 0; rewrite /= in_itv /= oppr_le0 hN0.
have [x0 [_ hmax]] := continuous_compact_maximum hne (@segment_compact R (- N) N) hcu.
exists (u x0 * total_variation g (- N) N)=> k [hk [hk0 hku]].
have hzk : forall x, k x <> 0 -> `|x| < N.
  move=> x hx; have hkx : 0 < k x.
    by rewrite lt_neqAle hk0 andbT eq_sym; apply/eqP.
  have hux : u x <> 0 by apply/eqP; rewrite gt_eqF // (lt_le_trans hkx (hku x)).
  by have := hz1 x hux; rewrite /N; lra.
have hexk : exists N', 0 <= N' /\ forall x, k x <> 0 -> `|x| <= N'.
  by exists N; split=> // x hx; exact: ltW (hzk x hx).
rewrite -(induced_daniell_eq (KR_continuous hk) hexk hN0 hzk).
apply: le_trans (ler_norm _) _.
apply: (stieltjes_integral_bound hg (KR_continuous hk) hN)=> x hx.
rewrite ger0_norm ?hk0 //; apply: le_trans (hku x) _; apply: hmax.
by rewrite /= in_itv.
Qed.

(** Source for [induced_daniell_linear]: mu is linear on K(R), Federer
    2.5.17, p. 111. *)
Theorem induced_daniell_linear : is_linear_functional_on_functions KR induced_daniell.
Proof.
split; first by move=> f1 f2 hf1 hf2; exact: induced_daniell_add.
by move=> c f hf; exact: induced_daniell_scale.
Qed.

(** Source for [induced_daniell_is_daniell]: mu is a Daniell integral on
    K(R), Federer 2.5.17, p. 111, by 2.5.13. *)
Theorem induced_daniell_is_daniell : is_daniell_integral KR induced_daniell.
Proof.
exact (compact_support_order_bounded_daniell (@Rhausdorff R) (@locally_compactR R) induced_daniell_linear
  induced_daniell_order_bounded).
Qed.

End InducedDaniell.
