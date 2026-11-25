(** Federer (1969), 2.5.17, p. 111: the condition psi^+{x : a < x < b} +
    psi^-{x : a < x < b} <= V_a^b g is obtained from the definition of the
    regular measures through sequences of functions in K(R) increasing to
    one on the open interval with supports in [a, b]. The functions f_n(x) =
    max{0, min{1, (n+1) min{x - a, b - x}}} serve as such a sequence; they
    are Lipschitzian, nonnegative, at most one, increasing in n, tend to one
    on the interval and vanish outside it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground ArchimedeanReciprocal FunctionLatticeUP
  DaniellCoverUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Bumps.
Variable R : realType.
Local Notation KR := (@compactly_supported_continuous_functions R R).

(** Source for [interval_bump]: the functions
    max{0, min{1, (n+1) min{x - a, b - x}}} increasing to the
    characteristic function of {x : a < x < b}, supporting Federer
    2.5.17, p. 111. *)
Definition interval_bump (a b : R) (n : nat) (x : R) : R :=
  Order.max 0 (Order.min 1 (n.+1%:R * Order.min (x - a) (b - x))).

(** Source for [interval_bump_ge0]: the bumps are nonnegative, Federer
    2.5.17, p. 111. *)
Lemma interval_bump_ge0 (a b : R) (n : nat) (x : R) : 0 <= interval_bump a b n x.
Proof. by rewrite /interval_bump le_max lexx. Qed.

(** Source for [interval_bump_le1]: the bumps are at most one, Federer
    2.5.17, p. 111. *)
Lemma interval_bump_le1 (a b : R) (n : nat) (x : R) : interval_bump a b n x <= 1.
Proof. by rewrite /interval_bump ge_max ler01 /= ge_min lexx. Qed.

(** Source for [interval_bump_zero]: the bumps vanish outside the open
    interval, Federer 2.5.17, p. 111. *)
Lemma interval_bump_zero (a b : R) (n : nat) (x : R) :
  ~~ (a < x < b) -> interval_bump a b n x = 0.
Proof.
move=> hn.
have hm : Order.min (x - a) (b - x) <= 0.
  move: hn; rewrite negb_and -!leNgt=> /orP[hxa|hbx]; rewrite ge_min.
  - by rewrite !subr_le0 hxa.
  - by rewrite !subr_le0 hbx orbT.
have hp : n.+1%:R * Order.min (x - a) (b - x) <= 0 by rewrite mulr_ge0_le0 // ler0n.
apply/le_anti; rewrite interval_bump_ge0 andbT /interval_bump ge_max lexx /= ge_min.
by rewrite hp orbT.
Qed.

(** Source for [interval_bump_support]: a nonzero value lies in the
    open interval, Federer 2.5.17, p. 111. *)
Lemma interval_bump_support (a b : R) (n : nat) (x : R) :
  interval_bump a b n x <> 0 -> a < x < b.
Proof. by move=> hne; apply: contraT=> hn; case: (hne (@interval_bump_zero a b n x hn)). Qed.

(** Source for [interval_bump_monotone]: the bumps increase with n,
    Federer 2.5.17, p. 111. *)
Lemma interval_bump_monotone (a b : R) (n m : nat) (x : R) :
  (n <= m)%N -> interval_bump a b n x <= interval_bump a b m x.
Proof.
move=> hnm; case: (boolP (a < x < b))=> [/andP[hax hxb]|hn]; last first.
  by rewrite !interval_bump_zero.
have hmm : 0 <= Order.min (x - a) (b - x) by rewrite le_min !subr_ge0 (ltW hax) (ltW hxb).
rewrite /interval_bump ge_max; apply/andP; split; first by rewrite le_max lexx.
rewrite le_max; apply/orP; right; rewrite le_min; apply/andP; split; first by rewrite ge_min lexx.
rewrite ge_min; apply/orP; right.
have hle : n.+1%:R <= m.+1%:R :> R by rewrite ler_nat.
exact (ler_wpM2r hmm hle).
Qed.

(** Source for [interval_bump_limit]: the bumps tend to one on the open
    interval, Federer 2.5.17, p. 111, by the Archimedean property. *)
Lemma interval_bump_limit (a b x : R) :
  a < x < b -> forall r : R, r < 1 -> exists n, r < interval_bump a b n x.
Proof.
move=> /andP[hax hxb] r hr.
have hmm : 0 < Order.min (x - a) (b - x) by rewrite lt_min !subr_gt0 hax hxb.
have hpos1 : 0 < `|r| + 1 by have := normr_ge0 r; lra.
have hpos : 0 < Order.min (x - a) (b - x) / (`|r| + 1) by rewrite divr_gt0.
have [n hn] := real_reciprocal_below hpos.
exists n; rewrite /interval_bump.
have hn' : `|r| + 1 < n.+1%:R * Order.min (x - a) (b - x).
  move: hn; rewrite ltr_pdivlMr // => hn.
  have hne : n.+1%:R != 0 :> R by rewrite pnatr_eq0.
  by rewrite -(ltr_pM2l (ltr0Sn R n)) mulrA (mulfV hne) mul1r in hn.
have hr' : r < n.+1%:R * Order.min (x - a) (b - x) by have := ler_norm r; lra.
by rewrite lt_max lt_min hr hr' orbT.
Qed.

(** Source for [max0_lipschitz]: supporting Lipschitz property of
    max{0, .}, Federer 2.5.17, p. 111. *)
Lemma max0_lipschitz (u v : R) : `|Order.max 0 u - Order.max 0 v| <= `|u - v|.
Proof.
have h1 := ler_norm (u - v); have h2 : v - u <= `|u - v| by rewrite distrC; exact: ler_norm.
rewrite !maxEle; case: (leP 0 u)=> hu; case: (leP 0 v)=> hv;
  rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [min1_lipschitz]: supporting Lipschitz property of
    min{1, .}, Federer 2.5.17, p. 111. *)
Lemma min1_lipschitz (u v : R) : `|Order.min 1 u - Order.min 1 v| <= `|u - v|.
Proof.
have h1 := ler_norm (u - v); have h2 : v - u <= `|u - v| by rewrite distrC; exact: ler_norm.
rewrite !minEle; case: (leP 1 u)=> hu; case: (leP 1 v)=> hv;
  rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [min_distance_lipschitz]: supporting Lipschitz property
    of min{x - a, b - x}, Federer 2.5.17, p. 111. *)
Lemma min_distance_lipschitz (a b x y : R) :
  `|Order.min (x - a) (b - x) - Order.min (y - a) (b - y)| <= `|x - y|.
Proof.
have h1 := ler_norm (x - y); have h2 : y - x <= `|x - y| by rewrite distrC; exact: ler_norm.
rewrite !minEle; case: (leP (x - a) (b - x))=> hx; case: (leP (y - a) (b - y))=> hy;
  rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [interval_bump_lipschitz]: the bumps are Lipschitzian
    with constant n+1, Federer 2.5.17, p. 111. *)
Lemma interval_bump_lipschitz (a b : R) (n : nat) (x y : R) :
  `|interval_bump a b n x - interval_bump a b n y| <= n.+1%:R * `|x - y|.
Proof.
rewrite /interval_bump.
apply: le_trans (max0_lipschitz _ _) _; apply: le_trans (min1_lipschitz _ _) _.
rewrite -mulrBr normrM ger0_norm ?ler0n //.
exact (ler_wpM2l (ler0n _ _) (min_distance_lipschitz a b x y)).
Qed.

(** Source for [lipschitz_continuous]: supporting continuity of a
    Lipschitzian real function, Federer 2.5.17, p. 111. *)
Lemma lipschitz_continuous (f : R -> R) (L : R) :
  0 <= L -> (forall x y, `|f x - f y| <= L * `|x - y|) ->
  continuous (f : R -> real_line_metric R).
Proof.
move=> hL hlip y; apply/cvg_ballP=> e he.
have hL1 : 0 < L + 1 by lra.
have he' : 0 < e / (L + 1) by rewrite divr_gt0.
near=> x; rewrite ballEmdist /= real_line_metric_distanceE.
apply: le_lt_trans (hlip y x) _.
have hx : `|y - x| < e / (L + 1).
  by near: x; have := nbhsx_ballx y (e / (L + 1)) he'; apply: filterS=> x' /=; rewrite /ball /=.
rewrite ltr_pdivlMr // in hx; apply: le_lt_trans _ hx; rewrite mulrC.
by apply: ler_wpM2l; [exact: normr_ge0 | rewrite lerDl ler01].
Unshelve. all: end_near.
Qed.

(** Source for [segment_closed_real]: supporting closedness of a
    segment of the real line, Federer 2.5.17, p. 111. *)
Lemma segment_closed_real (a b : R) : closed `[a, b].
Proof. exact (compact_closed (@Rhausdorff R) (@segment_compact R a b)). Qed.

(** Source for [interval_bump_member]: the bumps belong to K(R),
    Federer 2.5.17, p. 111: Lipschitzian with support in [a, b]. *)
Lemma interval_bump_member (a b : R) (n : nat) : KR (interval_bump a b n).
Proof.
split; first exact: lipschitz_continuous (ler0n _ _) (interval_bump_lipschitz a b n).
rewrite /real_function_support.
apply: (subclosed_compact (@closed_closure _ [set x | interval_bump a b n x <> 0])
  (@segment_compact R a b)).
rewrite [X in _ `<=` X]((closure_id _).1 (@segment_closed_real a b)).
apply: closureS=> x hx; have /andP[h1 h2] := interval_bump_support hx.
by rewrite /= in_itv /= (ltW h1) (ltW h2).
Qed.

(** Source for [interval_bump_suiting]: the bumps form a sequence
    suiting the open interval {x : a < x < b} in the sense of 2.5.2,
    p. 92, within K(R)+, Federer 2.5.17, p. 111. *)
Lemma interval_bump_suiting (a b : R) :
  is_daniell_suiting_sequence (positive_function_lattice KR) `]a, b[ (interval_bump a b).
Proof.
split; last split.
- move=> n; split; [split|]; first exact: interval_bump_member.
  + by move=> x; exact: interval_bump_ge0.
  + by move=> x; exact: interval_bump_ge0.
- by move=> n m hnm x; exact: interval_bump_monotone.
- by move=> x hx r hr; rewrite /= in_itv /= in hx; exact (interval_bump_limit hx hr).
Qed.

End Bumps.
