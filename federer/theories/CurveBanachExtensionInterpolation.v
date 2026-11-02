(** Federer (1969), 2.5.16, p. 110: the interpolation behind the extension
    of G to a Lipschitzian map H of R into a Banach space with Lip(H) =
    Lip(G). For a set S of real numbers and a map F of S into a complete
    normed space which is Lipschitzian on S, F extends continuously to the
    closure of S; on each bounded open interval disjoint from S whose end
    points lie in the closure of S the extension is affine, and on each
    unbounded such interval it is constant. The resulting map H is L
    Lipschitzian on R whenever F is L Lipschitzian on S. The map H is
    specified by the predicate [is_gap_interpolation]; its construction is
    local to the existence proof. the general interpolation lemma has no
    separate counterpart there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InterpolationAlgebra.
Variable R : realType.
Variable V : lmodType R.

(** Source for [interpolation_sub_right]: supporting identity for the
    affine interpolation B + c (A - B) of Federer 2.5.16, p. 110. *)
Lemma interpolation_sub_right (A B : V) (c : R) : B + c *: (A - B) - B = c *: (A - B).
Proof. by rewrite [B + _]addrC addrK. Qed.

(** Source for [interpolation_sub_left]: supporting identity for the
    affine interpolation of Federer 2.5.16, p. 110. *)
Lemma interpolation_sub_left (A B : V) (c : R) : B + c *: (A - B) - A = (1 - c) *: (B - A).
Proof. by rewrite scalerBl scale1r -[A - B]opprB scalerN addrAC. Qed.

(** Source for [interpolation_sub_same]: supporting identity for two
    values of the affine interpolation of Federer 2.5.16, p. 110. *)
Lemma interpolation_sub_same (A B : V) (c d : R) :
  (B + c *: (A - B)) - (B + d *: (A - B)) = (c - d) *: (A - B).
Proof. by rewrite opprD addrACA subrr add0r scalerBl. Qed.

(** Source for [interpolation_convex]: B + l (A - B) = l A + (1 - l) B,
    the printed form of the interpolation in Federer 2.5.16, p. 110. *)
Lemma interpolation_convex (A B : V) (l : R) : B + l *: (A - B) = l *: A + (1 - l) *: B.
Proof. by rewrite scalerBr scalerBl scale1r addrCA. Qed.

End InterpolationAlgebra.

Section GapInterpolationUP.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Local Notation Y := (real_norm_metric_space hN).

(** Source for [is_gap_interpolation]: the properties of the extension
    of a Lipschitzian map F on S to R in Federer 2.5.16, p. 110: H agrees
    with F on S and is the limit of F at the points of the closure of S;
    H is affine on every interval [a, b] disjoint from S except for its
    end points in the closure of S; H is constant below a lower bound and
    above an upper bound of S in the closure of S; and H is L Lipschitzian
    whenever F is L Lipschitzian on S. *)
Record is_gap_interpolation (S : set R) (F H : R -> Y) : Prop := {
  gap_interpolation_extends : forall u, S u -> H u = F u;
  gap_interpolation_limit : forall c, closure S c -> F @ within S (nbhs c) --> H c;
  gap_interpolation_affine : forall a b l, a <= b -> closure S a -> closure S b ->
    (forall u, a < u < b -> ~ S u) -> 0 <= l <= 1 ->
    H (l * a + (1 - l) * b) = l *: H a + (1 - l) *: H b;
  gap_interpolation_below : forall b, closure S b -> (forall u, S u -> b <= u) ->
    forall z, z <= b -> H z = H b;
  gap_interpolation_above : forall a, closure S a -> (forall u, S u -> u <= a) ->
    forall z, a <= z -> H z = H a;
  gap_interpolation_lipschitz : forall L, 0 <= L ->
    (forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) ->
    forall z w, mdist (H z) (H w) <= L * `|z - w|
}.

End GapInterpolationUP.

Section GapInterpolation.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Local Notation Y := (real_norm_metric_space hN).
Hypothesis hY : is_complete_metric_space Y.
Variable S : set R.
Variable F : R -> Y.
Variable L0 : R.
Hypothesis hF0 : forall u v, S u -> S v -> mdist (F u) (F v) <= L0 * `|u - v|.
Local Notation C := (closure S).

Let K := `|L0| + 1.

Let hK : 0 < K.
Proof. by rewrite /K ltr_pwDr // normr_ge0. Qed.

Let hFK (u v : R) : S u -> S v -> mdist (F u) (F v) <= K * `|u - v|.
Proof.
move=> hu hv; apply: le_trans (hF0 hu hv) _.
apply: ler_wpM2r; first exact: normr_ge0.
by apply: le_trans (ler_norm L0) _; rewrite /K lerDl.
Qed.

Let near_lipschitz (u t e : R) : S u -> S t -> `|u - t| < e / K -> mdist (F u) (F t) < e.
Proof.
move=> hu ht hut; apply: le_lt_trans (hFK hu ht) _.
by rewrite mulrC -ltr_pdivlMr.
Qed.

Let within_cauchy (c : R) : C c -> cauchy (F @ within S (nbhs c)).
Proof.
move=> hc.
have hP : ProperFilter (within S (nbhs c)) := within_nbhs_proper hc.
apply/(@cauchyP _ _ _ (fmap_proper_filter F hP))=> e he.
pose x := e / K.
have hx : 0 < x by rewrite /x divr_gt0.
pose d := x / 2.
have hd : 0 < d by rewrite /d divr_gt0.
have [u [hSu hu]] := hc (ball c d) (nbhsx_ballx c d hd).
exists (F u).
suff : nbhs c [set t | S t -> ball (F u) e (F t)] by [].
apply: (filterS _ (nbhsx_ballx c d hd))=> t hct hSt.
rewrite ballEmdist /=; apply: near_lipschitz=> //.
move: hu hct; rewrite /ball /= => h1 h2.
have h3 := ler_distD c u t; rewrite [`|u - c|]distrC in h3.
rewrite -/x; apply: le_lt_trans h3 _; rewrite /d in h1 h2; lra.
Qed.

Let within_limit_exists (c : R) : C c -> exists y : Y, F @ within S (nbhs c) --> y.
Proof.
by move=> hc; exact: hY _ (fmap_proper_filter F (within_nbhs_proper hc)) (within_cauchy hc).
Qed.

Let closure_value (c : R) : Y :=
  if pselect (exists y : Y, F @ within S (nbhs c) --> y) is left h then sval (cid h) else F c.

Let closure_value_cvg (c : R) : C c -> F @ within S (nbhs c) --> closure_value c.
Proof.
move=> hc; rewrite /closure_value; case: pselect=> [h|hn]; first exact: (svalP (cid h)).
by exfalso; apply: hn; exact: within_limit_exists hc.
Qed.

Let closure_value_extends (u : R) : S u -> closure_value u = F u.
Proof.
move=> hu; have hc : C u := subset_closure hu.
have hP : ProperFilter (within S (nbhs u)) := within_nbhs_proper hc.
have hlim : F @ within S (nbhs u) --> F u.
  apply/metricType_numDomainType.cvgrPdist_lt=> e he.
  suff : nbhs u [set t | S t -> mdist (F u) (F t) < e] by [].
  apply: (filterS _ (nbhsx_ballx u (e / K) (divr_gt0 he hK)))=> t hut hSt.
  exact: near_lipschitz.
exact (@cvg_unique Y (@metric_hausdorff _ Y) _ (fmap_proper_filter F hP) _ _ (closure_value_cvg hc) hlim).
Qed.

Let closure_value_approx (c e : R) : C c -> 0 < e ->
  exists u, S u /\ `|c - u| < e /\ mdist (closure_value c) (F u) < e.
Proof.
move=> hc he.
have hn : nbhs c [set t | S t -> mdist (closure_value c) (F t) < e].
  by move: (closure_value_cvg hc) => /metricType_numDomainType.cvgrPdist_lt /(_ e he).
have [u [hSu [hu1 hu2]]] := hc _ (filterI hn (nbhsx_ballx c e he)).
by exists u; split=> //; split; [exact: hu2 | exact: hu1].
Qed.

Let closure_value_lipschitz (L c d : R) : 0 <= L ->
  (forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) -> C c -> C d ->
  mdist (closure_value c) (closure_value d) <= L * `|c - d|.
Proof.
move=> hL hFL hc hd; apply/ler_addgt0Pr=> e he.
pose e' := e / (2 * (L + 1)).
have he' : 0 < e' by rewrite /e' divr_gt0 // mulr_gt0 // ltr_pwDr.
have [u [hu [hcu hFu]]] := closure_value_approx hc he'.
have [v [hv [hdv hFv]]] := closure_value_approx hd he'.
have h1 := metric_triangle (closure_value c) (F u) (closure_value d).
have h2 := metric_triangle (F u) (F v) (closure_value d).
have h3 := hFL u v hu hv.
have h4 : `|u - v| <= `|c - d| + 2 * e'.
  have := ler_distD c u v; have := ler_distD d c v; rewrite [`|u - c|]distrC.
  by move=> h5 h6; lra.
have h5 : L * `|u - v| <= L * `|c - d| + 2 * (L * e').
  by apply: le_trans (ler_wpM2l hL h4) _; rewrite mulrDr mulrCA lexx.
have he_eq : 2 * e' + 2 * (L * e') = e.
  by rewrite /e'; field; apply: lt0r_neq0; lra.
rewrite metric_sym in hFv.
by lra.
Qed.

Let closure_closure (A : set R) : A `<=` C -> closure A `<=` C.
Proof.
move=> hA x hx.
have hCC : closure C = C by apply/esym; apply: (closure_id C).1; exact: closed_closure.
by rewrite -hCC; exact: closureS hA x hx.
Qed.

Let sup_closure_mem (A : set R) : A `<=` C -> A !=set0 -> has_ubound A -> C (sup A).
Proof.
move=> hA hne hub; apply: (closure_closure hA).
move=> B /nbhs_ballP [e he hball].
have he' : 0 < e := he.
have hs : has_sup A by split.
have [a ha hlt] := sup_adherent he' hs.
exists a; split=> //; apply: hball.
have hle := sup_upper_bound hs ha.
by rewrite /ball /= ger0_norm ?subr_ge0 //; lra.
Qed.

Let inf_closure_mem (A : set R) : A `<=` C -> A !=set0 -> has_lbound A -> C (inf A).
Proof.
move=> hA hne hlb; apply: (closure_closure hA).
move=> B /nbhs_ballP [e he hball].
have he' : 0 < e := he.
have hi : has_inf A by split.
have [a ha hlt] := inf_adherent he' hi.
exists a; split=> //; apply: hball.
have hle := ge_inf hlb ha.
by rewrite /ball /= ler0_norm ?subr_le0 //; lra.
Qed.

Let left_part (z : R) : set R := [set c | C c /\ c <= z].
Let right_part (z : R) : set R := [set c | C c /\ z <= c].

Let left_anchor_mem (z : R) : left_part z !=set0 -> C (sup (left_part z)).
Proof. by move=> hne; apply: sup_closure_mem hne _; [move=> c [] | exists z=> c [_]]. Qed.

Let left_anchor_le (z : R) : left_part z !=set0 -> sup (left_part z) <= z.
Proof. by move=> hne; apply: ge_sup hne _ => c [_]. Qed.

Let left_anchor_upper (z c : R) : C c -> c <= z -> c <= sup (left_part z).
Proof.
move=> hc hcz; apply: sup_upper_bound; last by split.
by split; [exists c | exists z=> d [_]].
Qed.

Let right_anchor_mem (z : R) : right_part z !=set0 -> C (inf (right_part z)).
Proof. by move=> hne; apply: inf_closure_mem hne _; [move=> c [] | exists z=> c [_]]. Qed.

Let right_anchor_ge (z : R) : right_part z !=set0 -> z <= inf (right_part z).
Proof. by move=> hne; apply: lb_le_inf hne _ => c [_]. Qed.

Let right_anchor_lower (z c : R) : C c -> z <= c -> inf (right_part z) <= c.
Proof. by move=> hc hzc; apply: (ge_inf (E := right_part z)); [exists z=> d [_] | split]. Qed.

Let gap_open (z : R) : ~ C z -> forall c, C c -> c != z.
Proof. by move=> hz c hc; apply/eqP=> hcz; apply: hz; rewrite -hcz. Qed.

Let left_anchor_lt (z : R) : ~ C z -> left_part z !=set0 -> sup (left_part z) < z.
Proof.
move=> hz hne; rewrite lt_neqAle (left_anchor_le hne) andbT.
exact: gap_open hz _ (left_anchor_mem hne).
Qed.

Let right_anchor_gt (z : R) : ~ C z -> right_part z !=set0 -> z < inf (right_part z).
Proof.
move=> hz hne; rewrite lt_neqAle (right_anchor_ge hne) andbT eq_sym.
exact: gap_open hz _ (right_anchor_mem hne).
Qed.

Let H (z : R) : Y :=
  if pselect (C z) is left _ then closure_value z else
  if pselect (left_part z !=set0) is left _ then
    (if pselect (right_part z !=set0) is left _ then
      closure_value (inf (right_part z)) +
        ((inf (right_part z) - z) / (inf (right_part z) - sup (left_part z))) *:
        (closure_value (sup (left_part z)) - closure_value (inf (right_part z)))
    else closure_value (sup (left_part z)))
  else if pselect (right_part z !=set0) is left _ then closure_value (inf (right_part z))
  else F 0.

Let H_closure (c : R) : C c -> H c = closure_value c.
Proof. by move=> hc; rewrite /H; case: (pselect (C c)). Qed.

Let H_two_sided (z : R) : ~ C z -> left_part z !=set0 -> right_part z !=set0 ->
  H z = closure_value (inf (right_part z)) +
    ((inf (right_part z) - z) / (inf (right_part z) - sup (left_part z))) *:
    (closure_value (sup (left_part z)) - closure_value (inf (right_part z))).
Proof.
move=> hz hl hr; rewrite /H; case: (pselect (C z))=> [h|_]; first by case: (hz h).
case: (pselect (left_part z !=set0))=> [_|h]; last by case: (h hl).
by case: (pselect (right_part z !=set0))=> [_|h]; last by case: (h hr).
Qed.

Let H_left_only (z : R) : ~ C z -> left_part z !=set0 -> ~ (right_part z !=set0) ->
  H z = closure_value (sup (left_part z)).
Proof.
move=> hz hl hr; rewrite /H; case: (pselect (C z))=> [h|_]; first by case: (hz h).
case: (pselect (left_part z !=set0))=> [_|h]; last by case: (h hl).
by case: (pselect (right_part z !=set0))=> [h|_]; first by case: (hr h).
Qed.

Let H_right_only (z : R) : ~ C z -> ~ (left_part z !=set0) -> right_part z !=set0 ->
  H z = closure_value (inf (right_part z)).
Proof.
move=> hz hl hr; rewrite /H; case: (pselect (C z))=> [h|_]; first by case: (hz h).
case: (pselect (left_part z !=set0))=> [h|_]; first by case: (hl h).
by case: (pselect (right_part z !=set0))=> [_|h]; last by case: (h hr).
Qed.

Let H_none (z : R) : ~ C z -> ~ (left_part z !=set0) -> ~ (right_part z !=set0) -> H z = F 0.
Proof.
move=> hz hl hr; rewrite /H; case: (pselect (C z))=> [h|_]; first by case: (hz h).
case: (pselect (left_part z !=set0))=> [h|_]; first by case: (hl h).
by case: (pselect (right_part z !=set0))=> [h|_]; first by case: (hr h).
Qed.

Let norm_scale_dist (c : R) (A B : Y) : 0 <= c -> N (c *: (A - B)) = c * mdist A B.
Proof. by move=> hc; rewrite (real_seminorm_scale hN.1) ger0_norm. Qed.


Let anchors_lipschitz (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z : R) : left_part z !=set0 -> right_part z !=set0 ->
  mdist (closure_value (sup (left_part z))) (closure_value (inf (right_part z)))
    <= L * (inf (right_part z) - sup (left_part z)).
Proof.
move=> hl hr.
have h := closure_value_lipschitz hL hFL (left_anchor_mem hl) (right_anchor_mem hr).
by rewrite distrC ger0_norm ?subr_ge0 in h; [exact: h | apply: le_trans (right_anchor_ge hr); exact: left_anchor_le].
Qed.

Let H_dist_right (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z : R) : ~ C z -> right_part z !=set0 ->
  mdist (H z) (closure_value (inf (right_part z))) <= L * (inf (right_part z) - z).
Proof.
move=> hz hr.
have hbz := right_anchor_gt hz hr.
case: (pselect (left_part z !=set0))=> hl; last first.
  by rewrite (H_right_only hz hl hr) mdistxx mulr_ge0 // subr_ge0 ltW.
have haz := left_anchor_lt hz hl.
set a := sup (left_part z) in haz *; set b := inf (right_part z) in hbz *.
rewrite (H_two_sided hz hl hr) -/a -/b real_norm_metric_distanceE interpolation_sub_right.
have hc : 0 <= (b - z) / (b - a) by rewrite divr_ge0 // subr_ge0 ltW // (lt_trans haz hbz).
rewrite (norm_scale_dist _ _ hc).
have hab : 0 < b - a by rewrite subr_gt0 (lt_trans haz hbz).
apply: le_trans (ler_wpM2l hc (anchors_lipschitz hL hFL hl hr)) _; rewrite -/a -/b.
by rewrite mulrCA -mulrA mulVf ?lt0r_neq0 // mulr1 lexx.
Qed.

Let H_dist_left (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z : R) : ~ C z -> left_part z !=set0 ->
  mdist (H z) (closure_value (sup (left_part z))) <= L * (z - sup (left_part z)).
Proof.
move=> hz hl.
have haz := left_anchor_lt hz hl.
case: (pselect (right_part z !=set0))=> hr; last first.
  by rewrite (H_left_only hz hl hr) mdistxx mulr_ge0 // subr_ge0 ltW.
have hbz := right_anchor_gt hz hr.
set a := sup (left_part z) in haz *; set b := inf (right_part z) in hbz *.
rewrite (H_two_sided hz hl hr) -/a -/b real_norm_metric_distanceE interpolation_sub_left.
have hab : 0 < b - a by rewrite subr_gt0 (lt_trans haz hbz).
have hc : 1 - (b - z) / (b - a) = (z - a) / (b - a) by field; rewrite lt0r_neq0.
have hc0 : 0 <= (z - a) / (b - a) by apply: divr_ge0; rewrite subr_ge0 ltW // (lt_trans haz hbz).
rewrite hc (norm_scale_dist _ _ hc0) metric_sym.
apply: le_trans (ler_wpM2l hc0 (anchors_lipschitz hL hFL hl hr)) _; rewrite -/a -/b.
by rewrite mulrCA -mulrA mulVf ?lt0r_neq0 // mulr1 lexx.
Qed.

Let H_same_gap (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z w : R) : z <= w -> ~ C z -> ~ C w ->
  left_part z = left_part w -> right_part z = right_part w -> mdist (H z) (H w) <= L * (w - z).
Proof.
move=> hzw hz hw hl hr.
have hwz : 0 <= L * (w - z) by rewrite mulr_ge0 // subr_ge0.
case: (pselect (left_part z !=set0))=> hlz; case: (pselect (right_part z !=set0))=> hrz.
- have hlw : left_part w !=set0 by rewrite -hl.
  have hrw : right_part w !=set0 by rewrite -hr.
  rewrite (H_two_sided hz hlz hrz) (H_two_sided hw hlw hrw) -hl -hr.
  have haz := left_anchor_lt hz hlz; have hbz := right_anchor_gt hz hrz.
  have haw : sup (left_part z) < w by rewrite hl; exact: left_anchor_lt hw hlw.
  have hbw : w < inf (right_part z) by rewrite hr; exact: right_anchor_gt hw hrw.
  set a := sup (left_part z) in haz haw *; set b := inf (right_part z) in hbz hbw *.
  rewrite real_norm_metric_distanceE interpolation_sub_same.
  have hab : 0 < b - a by rewrite subr_gt0 (lt_trans haz hbz).
  have hcd : (b - z) / (b - a) - (b - w) / (b - a) = (w - z) / (b - a) by field; rewrite lt0r_neq0.
  have hc0 : 0 <= (w - z) / (b - a) by apply: divr_ge0; rewrite subr_ge0 // ltW // (lt_trans haz hbz).
  rewrite hcd (norm_scale_dist _ _ hc0).
  apply: le_trans (ler_wpM2l hc0 (anchors_lipschitz hL hFL hlz hrz)) _; rewrite -/a -/b.
  by rewrite mulrCA -mulrA mulVf ?lt0r_neq0 // mulr1 lexx.
- have hlw : left_part w !=set0 by rewrite -hl.
  have hrw : ~ (right_part w !=set0) by rewrite -hr.
  by rewrite (H_left_only hz hlz hrz) (H_left_only hw hlw hrw) hl mdistxx.
- have hlw : ~ (left_part w !=set0) by rewrite -hl.
  have hrw : right_part w !=set0 by rewrite -hr.
  by rewrite (H_right_only hz hlz hrz) (H_right_only hw hlw hrw) hr mdistxx.
- have hlw : ~ (left_part w !=set0) by rewrite -hl.
  have hrw : ~ (right_part w !=set0) by rewrite -hr.
  by rewrite (H_none hz hlz hrz) (H_none hw hlw hrw) mdistxx.
Qed.

Let H_lipschitz_closure_out (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z w : R) : z <= w -> C z -> ~ C w ->
  mdist (H z) (H w) <= L * (w - z).
Proof.
move=> hzw hz hw.
have hl : left_part w !=set0 by exists z.
have hza := left_anchor_upper hz hzw.
have haw := left_anchor_lt hw hl.
apply: le_trans (metric_triangle _ (closure_value (sup (left_part w))) _) _.
rewrite (H_closure hz) [X in _ + X]metric_sym.
have h1 := closure_value_lipschitz hL hFL hz (left_anchor_mem hl).
rewrite distrC ger0_norm ?subr_ge0 // in h1.
have h2 := H_dist_left hL hFL hw hl.
by apply: le_trans (lerD h1 h2) _; rewrite -mulrDr; apply: (ler_wpM2l hL); lra.
Qed.

Let H_lipschitz_out_closure (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z w : R) : z <= w -> ~ C z -> C w ->
  mdist (H z) (H w) <= L * (w - z).
Proof.
move=> hzw hz hw.
have hr : right_part z !=set0 by exists w.
have hbw := right_anchor_lower hw hzw.
have hzb := right_anchor_gt hz hr.
apply: le_trans (metric_triangle _ (closure_value (inf (right_part z))) _) _.
rewrite (H_closure hw).
have h1 := H_dist_right hL hFL hz hr.
have h2 := closure_value_lipschitz hL hFL (right_anchor_mem hr) hw.
rewrite distrC ger0_norm ?subr_ge0 // in h2.
by apply: le_trans (lerD h1 h2) _; rewrite -mulrDr; apply: (ler_wpM2l hL); lra.
Qed.

Let H_lipschitz_le (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z w : R) : z <= w -> mdist (H z) (H w) <= L * (w - z).
Proof.
move=> hzw.
case: (pselect (C z))=> hz; case: (pselect (C w))=> hw.
- rewrite (H_closure hz) (H_closure hw).
  by have := closure_value_lipschitz hL hFL hz hw; rewrite distrC ger0_norm ?subr_ge0.
- exact: (H_lipschitz_closure_out hL hFL).
- exact: (H_lipschitz_out_closure hL hFL).
case: (pselect (exists c, C c /\ z <= c <= w))=> [[c [hc /andP[hzc hcw]]]|hnone].
  apply: le_trans (metric_triangle _ (H c) _) _.
  have h1 := H_lipschitz_out_closure hL hFL hzc hz hc.
  have h2 := H_lipschitz_closure_out hL hFL hcw hc hw.
  by apply: le_trans (lerD h1 h2) _; rewrite -mulrDr; apply: (ler_wpM2l hL); lra.
have hl : left_part z = left_part w.
  apply/seteqP; split=> c [hc hcz]; split=> //; first exact: le_trans hcz hzw.
  rewrite leNgt; apply/negP=> hzc; apply: hnone; exists c; split=> //.
  by rewrite (ltW hzc).
have hr : right_part z = right_part w.
  apply/seteqP; split=> c [hc hzc]; split=> //; last exact: le_trans hzw hzc.
  rewrite leNgt; apply/negP=> hcw; apply: hnone; exists c; split=> //.
  by rewrite hzc (ltW hcw).
exact: (H_same_gap hL hFL).
Qed.

Let H_lipschitz (L : R) (hL : 0 <= L)
    (hFL : forall u v, S u -> S v -> mdist (F u) (F v) <= L * `|u - v|) (z w : R) : mdist (H z) (H w) <= L * `|z - w|.
Proof.
case: (leP z w)=> hzw.
  by rewrite distrC ger0_norm ?subr_ge0 //; exact: (H_lipschitz_le hL hFL).
rewrite ger0_norm ?subr_ge0 ?(ltW hzw) // metric_sym.
exact: (H_lipschitz_le hL hFL (ltW hzw)).
Qed.



Let closure_gap (a b : R) : (forall u, a < u < b -> ~ S u) -> forall c, C c -> ~ (a < c < b).
Proof.
move=> hgap c hc /andP[hac hcb].
pose r := Order.min (c - a) (b - c).
have hr : 0 < r by rewrite /r lt_min !subr_gt0 hac hcb.
have [u [hSu hu]] := hc (ball c r) (nbhsx_ballx c r hr).
have hra : r <= c - a by rewrite /r ge_min lexx.
have hrb : r <= b - c by rewrite /r ge_min lexx orbT.
apply: (hgap u) hSu; move: hu; rewrite /ball /= ltr_norml => /andP[h1 h2].
by apply/andP; split; lra.
Qed.

Let H_affine (a b l : R) : a <= b -> C a -> C b -> (forall u, a < u < b -> ~ S u) -> 0 <= l <= 1 ->
  H (l * a + (1 - l) * b) = l *: H a + (1 - l) *: H b.
Proof.
move=> hab ha hb hgap /andP[hl0 hl1].
have hcg := closure_gap hgap.
case: (eqVneq l 1)=> [->|hl1'].
  by rewrite mul1r subrr mul0r addr0 scale1r scale0r addr0.
case: (eqVneq l 0)=> [->|hl0'].
  by rewrite mul0r add0r subr0 mul1r scale0r add0r scale1r.
case: (eqVneq a b)=> [<-|hab'].
  have h1 : l + (1 - l) = 1 by rewrite addrC subrK.
  by rewrite -mulrDl h1 mul1r -scalerDl h1 scale1r.
have hlt0 : 0 < l by rewrite lt_neqAle eq_sym hl0' hl0.
have hlt1 : l < 1 by rewrite lt_neqAle hl1' hl1.
have hablt : a < b by rewrite lt_neqAle hab' hab.
set z := l * a + (1 - l) * b.
have haz : a < z.
  rewrite /z; have : 0 < (1 - l) * (b - a) by rewrite mulr_gt0 // subr_gt0.
  by rewrite mulrBr; lra.
have hzb : z < b.
  rewrite /z; have : 0 < l * (b - a) by rewrite mulr_gt0 // subr_gt0.
  by rewrite mulrBr; lra.
have hz : ~ C z by move=> hcz; apply: (hcg z hcz); rewrite haz hzb.
have hl : left_part z !=set0 by exists a; split=> //; exact: ltW.
have hr : right_part z !=set0 by exists b; split=> //; exact: ltW.
have hsup : sup (left_part z) = a.
  apply/le_anti; rewrite (left_anchor_upper ha (ltW haz)) andbT.
  apply: ge_sup hl _ => c [hc hcz]; rewrite leNgt; apply/negP=> hac.
  by apply: (hcg c hc); rewrite hac (le_lt_trans hcz hzb).
have hinf : inf (right_part z) = b.
  apply/le_anti; rewrite (right_anchor_lower hb (ltW hzb)) /=.
  apply: lb_le_inf hr _ => c [hc hzc]; rewrite leNgt; apply/negP=> hcb.
  by apply: (hcg c hc); rewrite hcb (lt_le_trans haz hzc).
rewrite (H_two_sided hz hl hr) hsup hinf (H_closure ha) (H_closure hb).
have hcoef : (b - z) / (b - a) = l by rewrite /z; field; rewrite subr_eq0 eq_sym.
by rewrite hcoef interpolation_convex.
Qed.

Let H_below (b : R) : C b -> (forall u, S u -> b <= u) -> forall z, z <= b -> H z = H b.
Proof.
move=> hb hlow z hzb.
have hCge : forall c, C c -> b <= c.
  move=> c hc; rewrite leNgt; apply/negP=> hcb.
  have hr : 0 < b - c by rewrite subr_gt0.
  have [u [hSu hu]] := hc (ball c (b - c)) (nbhsx_ballx c (b - c) hr).
  have := hlow u hSu; move: hu; rewrite /ball /= ltr_norml => /andP[h1 h2] h3; lra.
move: hzb; rewrite le_eqVlt => /orP[/eqP->//|hzb].
have hz : ~ C z by move=> hcz; have := hCge z hcz; rewrite leNgt hzb.
have hl : ~ (left_part z !=set0).
  by move=> [c [hc hcz]]; have := hCge c hc; rewrite leNgt (le_lt_trans hcz hzb).
have hr : right_part z !=set0 by exists b; split=> //; exact: ltW.
have hinf : inf (right_part z) = b.
  apply/le_anti; rewrite (right_anchor_lower hb (ltW hzb)) /=.
  by apply: lb_le_inf hr _ => c [hc _]; exact: hCge.
by rewrite (H_right_only hz hl hr) hinf (H_closure hb).
Qed.

Let H_above (a : R) : C a -> (forall u, S u -> u <= a) -> forall z, a <= z -> H z = H a.
Proof.
move=> ha hup z haz.
have hCle : forall c, C c -> c <= a.
  move=> c hc; rewrite leNgt; apply/negP=> hac.
  have hr : 0 < c - a by rewrite subr_gt0.
  have [u [hSu hu]] := hc (ball c (c - a)) (nbhsx_ballx c (c - a) hr).
  have := hup u hSu; move: hu; rewrite /ball /= ltr_norml => /andP[h1 h2] h3; lra.
move: haz; rewrite le_eqVlt => /orP[/eqP<-//|haz].
have hz : ~ C z by move=> hcz; have := hCle z hcz; rewrite leNgt haz.
have hr : ~ (right_part z !=set0).
  by move=> [c [hc hzc]]; have := hCle c hc; rewrite leNgt (lt_le_trans haz hzc).
have hl : left_part z !=set0 by exists a; split=> //; exact: ltW.
have hsup : sup (left_part z) = a.
  apply/le_anti; rewrite (left_anchor_upper ha (ltW haz)) andbT.
  by apply: ge_sup hl _ => c [hc _]; exact: hCle.
by rewrite (H_left_only hz hl hr) hsup (H_closure ha).
Qed.

(** Source for [gap_interpolation_exists]: existence of the extension of
    Federer 2.5.16, p. 110, for a Lipschitzian map F on a set S of real
    numbers with values in a complete normed space. *)
Theorem gap_interpolation_exists : exists H : R -> Y, is_gap_interpolation S F H.
Proof.
exists H; constructor.
- by move=> u hu; rewrite (H_closure (subset_closure hu)) closure_value_extends.
- by move=> c hc; rewrite (H_closure hc); exact: closure_value_cvg.
- exact: H_affine.
- exact: H_below.
- exact: H_above.
- by move=> L hL hFL; exact: (H_lipschitz hL hFL).
Qed.

End GapInterpolation.
