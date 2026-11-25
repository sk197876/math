(** Federer (1969), 2.7.16, printed pp. 133–134: "If dim V < oo, then dim
    A(V, V) < oo and all norms on A(V, V) induce the same locally compact
    topology. In particular we can choose an inner product on V and norm
    Hom(V, V) as in 1.7.6." This module supplies the topology of Hom(V, W)
    for a space V with an inner product and a finite basis and a space W
    with an inner product. The topology is that of the inner product of
    Hom(V, W) of 1.7.9, p. 35 (HomInner.v). By the two inequalities ||f|| <=
    |f| <= (dim V)^{1/2} ||f|| of 1.7.9 the neighbourhoods are equally
    described by the operator norm of 1.7.6, p. 33
    (hom_space_nbhs_operator), which is the norm used by Federer for the
    estimates of composition and inversion. When W also has a finite basis,
    closed bounded subsets of Hom(V, W) are compact, by the argument of
    1.7.1, p. 28, applied to the synthesis (w_1, ..., w_n) |-> sum_i (x |->
    (x . e_i) w_i) for an orthonormal base e of V; hence Hom(V, W) is
    locally compact and its additive group is a locally compact Hausdorff
    topological group (2.7.1, p. 121). Evaluation (f, x) |-> f(x) is
    continuous. The equivalence of all norms on a finite dimensional space
    is not formalised; only the two norms of 1.7.6 and 1.7.9 are compared.
     *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology InnerBoundedness InnerNormalization InnerFiniteSynthesis InnerFiniteCompactness
  OrthonormalFamilies OrthonormalisationUP GramSchmidt LinearBasis Bilinear TensorUP Hom HomInner
  HomInnerCoordinates HomOperatorNorm OperatorNormUP OperatorNormLaws OperatorNorm
  TopologicalGroupUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OperatorNormRules.
Variable R : realType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [linear_operator_norm_ext]: Federer 1.7.6, p. 33: the
    norm ||f|| = sup{|f(x)| : |x| <= 1} depends only on the values of f.
    Supporting lemma for 2.7.16, p. 134. *)
Lemma linear_operator_norm_ext (f g : {linear V -> U}) :
  f =1 g -> linear_operator_norm hB hC hb f = linear_operator_norm hB hC hb g.
Proof.
move=> hfg; apply: (operator_norm_unique (linear_operator_normP hB hC hb f)).
have [hu [x [hx hfx]]] := linear_operator_normP hB hC hb g.
by split=> [y hy|]; [rewrite hfg; exact: hu|exists x; rewrite hfg].
Qed.

(** Source for [linear_operator_norm_least]: Federer 1.7.6, p. 33: if
    0 <= M and |f(x)| <= M |x| for every x, then ||f|| <= M. Supporting
    lemma for 2.7.16, p. 134. *)
Lemma linear_operator_norm_least (f : {linear V -> U}) (M : R) :
  0 <= M -> (forall x, inner_norm hC (f x) <= M * inner_norm hB x) ->
  linear_operator_norm hB hC hb f <= M.
Proof.
move=> hM h; apply/(operator_norm_le_unit (linear_operator_normP hB hC hb f))=> x hx.
by apply: le_trans (h x) _; rewrite -[X in _ <= X]mulr1 ler_wpM2l.
Qed.

End OperatorNormRules.

Section HomSpace.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hC hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation WT := (inner_metric_space hC).

(** Source for [hom_operator_norm]: "norm Hom(V, V) as in 1.7.6",
    Federer 2.7.16, p. 134: the operator norm ||f|| of 1.7.6, p. 33, of a
    member f of Hom(V, W). Definition. *)
Definition hom_operator_norm (f : Hom V W) : R := linear_operator_norm hB hC hb (hom_as_linear f).

Local Notation onorm := hom_operator_norm.

(** Source for [hom_operator_norm_nonnegative]: Federer 1.7.6, p. 33,
    0 <= ||f||. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_nonnegative (f : Hom V W) : 0 <= onorm f.
Proof. exact: linear_operator_norm_nonnegative. Qed.

(** Source for [hom_operator_norm_bound]: Federer 1.7.6, pp. 33–34,
    |f(x)| <= ||f|| |x|. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_bound (f : Hom V W) (x : V) :
  inner_norm hC (f x) <= onorm f * inner_norm hB x.
Proof. exact: (linear_operator_norm_bound hB hC hb (hom_as_linear f) x). Qed.

(** Source for [hom_operator_norm_least]: Federer 1.7.6, p. 33: if
    0 <= M and |f(x)| <= M |x| for every x, then ||f|| <= M. Supporting
    lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_least (f : Hom V W) (M : R) :
  0 <= M -> (forall x, inner_norm hC (f x) <= M * inner_norm hB x) -> onorm f <= M.
Proof.
move=> hM h; rewrite /hom_operator_norm.
by apply: (@linear_operator_norm_least R V W B C hB hC n b hb (hom_as_linear f) M hM).
Qed.

(** Source for [hom_operator_norm_add]: the triangle inequality
    ||f + g|| <= ||f|| + ||g|| of the operator norm of 1.7.6, p. 33.
    Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_add (f g : Hom V W) : onorm (f + g) <= onorm f + onorm g.
Proof.
apply: hom_operator_norm_least; first by rewrite addr_ge0 ?hom_operator_norm_nonnegative.
move=> x; rewrite hom_addE mulrDl; apply: le_trans (inner_norm_triangle hC _ _) _.
by apply: lerD; exact: hom_operator_norm_bound.
Qed.

(** Source for [hom_operator_norm_opp]: ||-f|| = ||f||, Federer 1.7.6,
    p. 33. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_opp (f : Hom V W) : onorm (- f) = onorm f.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; apply: hom_operator_norm_least;
  rewrite ?hom_operator_norm_nonnegative // => x.
- have -> : (- f) x = - f x by [].
  by rewrite inner_normN; exact: hom_operator_norm_bound.
- have -> : f x = - (- f) x by rewrite opprK.
  by rewrite inner_normN; exact: hom_operator_norm_bound.
Qed.

(** Source for [hom_operator_norm_distC]: ||f - g|| = ||g - f||, Federer
    1.7.6, p. 33. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_distC (f g : Hom V W) : onorm (f - g) = onorm (g - f).
Proof. by rewrite -hom_operator_norm_opp opprB. Qed.

(** Source for [hom_operator_norm_sub_bound]: ||g|| <= ||f|| + ||g - f||,
    Federer 1.7.6, p. 33. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_operator_norm_sub_bound (f g : Hom V W) : onorm g <= onorm f + onorm (g - f).
Proof. by have := hom_operator_norm_add f (g - f); rewrite addrC subrK. Qed.

(** Source for [hom_space_normE]: Federer 1.7.9, p. 35: the norm of the
    topology of Hom(V, W) is the norm |f| of the inner product of
    1.7.9. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_space_normE (f : H) : `|f| = hom_norm hB hC hb f.
Proof. by []. Qed.

(** Source for [hom_space_operator_le]: Federer 1.7.9, p. 35,
    ||f|| <= |f|. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_space_operator_le (f : H) : onorm f <= `|f|.
Proof. exact: (hom_operator_norm_comparison hB hC hb f).1. Qed.

(** Source for [hom_space_le_operator]: Federer 1.7.9, p. 35,
    |f| <= (dim V)^{1/2} ||f||. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_space_le_operator (f : H) : `|f| <= Num.sqrt n%:R * onorm f.
Proof. exact: (hom_operator_norm_comparison hB hC hb f).2. Qed.

(** Source for [hom_space_nbhs_operator]: "we can choose an inner product
    on V and norm Hom(V, V) as in 1.7.6", Federer 2.7.16, p. 134: a set A
    is a neighbourhood of f in Hom(V, W) if and only if it contains
    {g : ||g - f|| < r} for some r > 0, so that the topology is the
    operator norm topology. Direct formalisation for the two norms of
    1.7.6 and 1.7.9. *)
Theorem hom_space_nbhs_operator (f : H) (A : set H) :
  nbhs f A <-> exists2 r : R, 0 < r & forall g : H, onorm (g - f) < r -> A g.
Proof.
split.
- move=> /nbhs_normP [e he hA].
  have hs : (0 : R) < Num.sqrt n%:R + 1 by apply: ltr_wpDl; [exact: sqrtr_ge0|exact: ltr01].
  exists (e / (Num.sqrt n%:R + 1)); first by rewrite divr_gt0.
  move=> g hg; apply: hA; rewrite /ball_ /= distrC.
  apply: le_lt_trans (hom_space_le_operator (g - f)) _.
  apply: (@le_lt_trans _ _ ((Num.sqrt n%:R + 1) * onorm (g - f))).
    by rewrite ler_wpM2r ?hom_operator_norm_nonnegative // lerDl.
  by rewrite mulrC -ltr_pdivlMr.
- move=> [r hr hA]; apply/nbhs_ballP; exists r=> // g; rewrite -ball_normE /= => hg.
  apply: hA; apply: le_lt_trans (hom_space_operator_le (g - f)) _.
  by rewrite distrC in hg.
Qed.

(** Source for [hom_space_operator_ball_nbhs]: Federer 2.7.16, p. 134:
    {g : ||g - f|| < r} is a neighbourhood of f for r > 0. Supporting
    lemma. *)
Lemma hom_space_operator_ball_nbhs (f : H) (r : R) : 0 < r ->
  nbhs f [set g : H | onorm (g - f) < r].
Proof. by move=> hr; apply/hom_space_nbhs_operator; exists r. Qed.

(** Source for [hom_space_hausdorff]: Hom(V, W) is Hausdorff, being a
    metric space by 1.7.1 and 1.7.9, pp. 28 and 35, as required in
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma hom_space_hausdorff : hausdorff_space H.
Proof. exact: (@metric_hausdorff R [the metricType R of H]). Qed.

(** Source for [hom_evaluation_continuous]: the map (f, x) |-> f(x) of
    Hom(V, W) x V into W is continuous, since
    |g(y) - f(x)| <= ||g|| |y - x| + ||g - f|| |x|, Federer 1.7.6,
    p. 33; it supports the continuity of the actions of 2.7.16,
    pp. 134–140. Supporting lemma. *)
Lemma hom_evaluation_continuous : continuous (fun p : H * VT => ((p.1 : Hom V W) p.2 : WT)).
Proof.
move=> [f x]; apply/cvgrPdist_lt=> eps heps.
pose c := onorm f + inner_norm hB x + 1.
have hc : 0 < c.
  by apply: ltr_wpDl; [rewrite addr_ge0 ?hom_operator_norm_nonnegative ?inner_norm_nonnegative|exact: ltr01].
pose d := Num.min 1 (eps / (c * 2)).
have hd : 0 < d by rewrite /d lt_min ltr01 divr_gt0 ?mulr_gt0.
have hd1 : d <= 1 by rewrite /d ge_min lexx.
have hd2 : d * c < eps.
  apply: (@le_lt_trans _ _ (eps / (c * 2) * c)); first by rewrite ler_wpM2r ?(ltW hc) // /d ge_min lexx orbT.
  rewrite invfM mulrAC mulrA mulfK ?gt_eqF //.
  by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
exists (ball f d, ball x d); first by split; exact: nbhsx_ballx.
move=> [g y] [/= hg hy].
have hg' : onorm (g - f) < d.
  apply: le_lt_trans (hom_space_operator_le _) _.
  by move: hg; rewrite -ball_normE /= distrC.
have hy' : inner_norm hB (y - x) < d by move: hy; rewrite -ball_normE /= distrC.
rewrite -ball_normE /= in hg hy.
have he : (f x : WT) - g y = - (((g - f : H) : Hom V W) x + (g : Hom V W) (y - x)).
  have h1 : ((g - f : H) : Hom V W) x = g x - f x by [].
  have h2 : (g : Hom V W) (y - x) = g y - g x by exact: (linearB (hom_as_linear g) y x).
  by rewrite h1 h2 [g x - f x + _]addrC addrA subrK opprB.
change (inner_norm hC ((f x : WT) - g y) < eps); rewrite he inner_normN.
apply: le_lt_trans (inner_norm_triangle hC _ _) _.
apply: le_lt_trans hd2.
apply: (@le_trans _ _ (onorm (g - f) * inner_norm hB x + onorm g * inner_norm hB (y - x))).
  by apply: lerD; exact: hom_operator_norm_bound.
have hgn : onorm g <= onorm f + 1.
  apply: le_trans (hom_operator_norm_sub_bound f g) _; rewrite lerD2l.
  exact: le_trans (ltW hg') hd1.
rewrite /c mulrDr mulrDr mulr1 [d * onorm f + _]addrC -addrA.
apply: (@le_trans _ _ (d * inner_norm hB x + (onorm f + 1) * d)).
  apply: lerD.
    by rewrite ler_wpM2r ?inner_norm_nonnegative // ltW.
  by apply: ler_pM; rewrite ?hom_operator_norm_nonnegative ?inner_norm_nonnegative // ltW.
by rewrite mulrDl mul1r [d * onorm f]mulrC.
Qed.

(** Source for [hom_additive_group_laws]: the additive group of
    Hom(V, W), Federer 2.7.16, p. 136, with the group laws of 2.7.1,
    p. 121. Supporting lemma. *)
Lemma hom_additive_group_laws : is_group_laws (fun f g : H => f + g) (fun f => - f) 0.
Proof. by split; [exact: addrA | exact: add0r | exact: addNr]. Qed.

(** Source for [hom_additive_topological_group]: the additive group of
    Hom(V, W) is a topological group, Federer 2.7.16, p. 136, in the
    sense of 2.7.1, p. 121. Supporting lemma. *)
Lemma hom_additive_topological_group :
  is_topological_group (fun f g : H => f + g) (fun f => - f) 0.
Proof.
split; first exact: hom_additive_group_laws.
- exact: add_continuous.
- exact: oppr_continuous.
Qed.

(** Source for [hom_rank_one_fun]: the map x |-> (x . a) y of V into W,
    the composition of the covector x |-> x . a with y, supporting the
    compactness argument of Federer 1.7.1, p. 28, for Hom(V, W) in
    2.7.16, p. 134. Definition of the function. *)
Definition hom_rank_one_fun (a : V) (y : W) (x : V) : W := (B x a : R) *: y.

(** Source for [hom_rank_one_linear]: the map x |-> (x . a) y is linear,
    supporting Federer 2.7.16, p. 134. *)
Lemma hom_rank_one_linear (a : V) (y : W) : linear (hom_rank_one_fun a y).
Proof.
move=> t x z; rewrite /hom_rank_one_fun (bilDl (inner_bilinear hB)) (bilZl (inner_bilinear hB)).
by rewrite scalerDl scalerA.
Qed.

(** Source for [hom_rank_one]: the member x |-> (x . a) y of Hom(V, W),
    supporting Federer 2.7.16, p. 134. Definition. *)
Definition hom_rank_one (a : V) (y : W) : Hom V W :=
  @HomMap R V W (hom_rank_one_fun a y) (introT (asboolP _) (hom_rank_one_linear a y)).

(** Source for [hom_rank_oneE]: the value (x . a) y of the map
    x |-> (x . a) y, supporting Federer 2.7.16, p. 134. *)
Lemma hom_rank_oneE (a : V) (y : W) (x : V) : hom_rank_one a y x = (B x a : R) *: y.
Proof. by []. Qed.

(** Source for [hom_rank_one_operator_norm]: the operator norm of
    x |-> (x . a) y is at most |a| |y|, by Cauchy's inequality and
    Federer 1.7.6, p. 33. Supporting lemma for 2.7.16, pp. 134–135. *)
Lemma hom_rank_one_operator_norm (a : V) (y : W) :
  onorm (hom_rank_one a y) <= inner_norm hB a * inner_norm hC y.
Proof.
apply: hom_operator_norm_least; first by rewrite mulr_ge0 ?inner_norm_nonnegative.
move=> x; rewrite hom_rank_oneE inner_normZ mulrAC ler_wpM2r ?inner_norm_nonnegative //.
by rewrite mulrC; exact: inner_cauchy.
Qed.

(** Source for [hom_rank_one_continuous]: y |-> (x |-> (x . a) y) is
    continuous from W into Hom(V, W), since its operator norm is at most
    |a| |y|, Federer 1.7.6, p. 33. Supporting lemma for 2.7.16, p. 134. *)
Lemma hom_rank_one_continuous (a : V) : continuous (fun y : WT => (hom_rank_one a y : H)).
Proof.
move=> y; apply/(@cvgrPdist_lt _ _ _ (nbhs y) (nbhs_filter y))=> eps heps.
pose s := Num.sqrt n%:R * inner_norm hB a + 1.
have hs : 0 < s.
  by apply: ltr_wpDl; [rewrite mulr_ge0 ?sqrtr_ge0 ?inner_norm_nonnegative|exact: ltr01].
have hd : 0 < eps / s by rewrite divr_gt0.
apply: (filterS _ (nbhsx_ballx y _ hd))=> z; rewrite -ball_normE /= => hz.
have hdiff : (hom_rank_one a y : H) - hom_rank_one a z = hom_rank_one a (y - z).
  apply: hom_ext=> x.
  have -> : (((hom_rank_one a y : H) - hom_rank_one a z : H) : Hom V W) x =
    hom_rank_one a y x - hom_rank_one a z x by [].
  by rewrite !hom_rank_oneE scalerBr.
rewrite hdiff; apply: le_lt_trans (hom_space_le_operator _) _.
have hb' := hom_rank_one_operator_norm a (y - z).
apply: (@le_lt_trans _ _ (Num.sqrt n%:R * (inner_norm hB a * inner_norm hC (y - z)))).
  by rewrite ler_wpM2l ?sqrtr_ge0.
apply: (@le_lt_trans _ _ (s * inner_norm hC (y - z))).
  by rewrite mulrA ler_wpM2r ?inner_norm_nonnegative // lerDl.
by rewrite mulrC -ltr_pdivlMr.
Qed.

Variable k : nat.
Variable c : 'I_k -> W.
Hypothesis hc : is_basis c.

(** Source for [hom_space_boundedly_compact]: "all norms on A(V, V)
    induce the same locally compact topology", Federer 2.7.16, p. 134,
    for Hom(V, W) with finite dimensional V and W: closed bounded sets
    are compact, by the argument of 1.7.1, p. 28. For an orthonormal base
    e of V the map (w_i)_i |-> sum_i (x |-> (x . e_i) w_i) is continuous,
    maps the product of the closed balls {w : |w| <= r} onto a compact set
    and sends (f(e_i))_i to f, while |f(e_i)| <= ||f|| <= |f|. Direct
    formalisation of the local compactness, by a different route from the
    equivalence of norms. *)
Theorem hom_space_boundedly_compact : inner_boundedly_compact (hom_inner_productP hB hC hb).
Proof.
move=> A hA [r hr].
have [e [he heo]] := orthonormal_basis_exists hB hb.
have ho := orthonormalisation_orthonormal heo.
pose S (w : 'I_n -> WT) : H := \sum_i (hom_rank_one (e i) (w i) : H).
have hS : continuous S.
  apply: continuous_big; first exact: add_continuous.
  move=> i _ w; apply: (@continuous_comp _ _ _ (fun w : 'I_n -> WT => w i)).
    exact: proj_continuous.
  exact: hom_rank_one_continuous.
pose Q : set ('I_n -> WT) := [set w | forall i, w i \in [set y : WT | inner_norm hC y <= r]].
have hQ : compact Q.
  have hcb := @inner_finite_basis_boundedly_compact R W C hC k c hc.
  have hK : forall i : 'I_n, compact [set y : WT | inner_norm hC y <= r].
    move=> _; apply: hcb; first exact: inner_norm_sublevel_closed.
    by exists r.
  have ht := @tychonoff _ (fun _ : 'I_n => WT) (fun _ => [set y : WT | inner_norm hC y <= r]) hK.
  have -> : Q = [set w : 'I_n -> WT | forall i, [set y : WT | inner_norm hC y <= r] (w i)].
    by apply/seteqP; split=> w hw i; [exact: set_mem (hw i)|exact: mem_set (hw i)].
  exact: ht.
have hc' : compact (S @` Q) by apply: continuous_compact; [exact: continuous_subspaceT|exact: hQ].
apply: (subclosed_compact hA hc')=> f hf.
exists (fun i => (f : Hom V W) (e i)).
  move=> i; apply: mem_set; rewrite /=.
  apply: le_trans (hr f hf).
  apply: (@le_trans _ _ (onorm f)); last exact: hom_space_operator_le.
  apply: le_trans (hom_operator_norm_bound f (e i)) _.
  by rewrite (@orthonormal_norm1 R V B hB (Finite.clone 'I_n _) e ho i) mulr1.
apply: hom_ext=> x.
have hsum : forall (F : 'I_n -> H) (z : V), ((\sum_i F i : H) : Hom V W) z = \sum_i (F i : Hom V W) z.
  move=> F z; elim/big_rec2: _=> [//|i y G _ <-].
  by rewrite hom_addE.
rewrite /S hsum.
have hx := @inner_finite_synthesis_coordinates R V B hB n e he ho x.
rewrite /inner_finite_synthesis in hx.
have hl : forall z : V, (f : Hom V W) z = hom_as_linear f z by [].
rewrite -{2}hx [in RHS]hl linear_sum; apply: eq_bigr=> i _.
by rewrite linearZ_LR hom_rank_oneE inner_coordinateE.
Qed.

(** Source for [hom_space_closed_ball_compact]: the closed balls
    {g : |g - f| <= r} of Hom(V, W) are compact, Federer 2.7.16, p. 134,
    by 1.7.1, p. 28. Supporting lemma. *)
Lemma hom_space_closed_ball_compact (f : H) (r : R) : compact [set g : H | `|g - f| <= r].
Proof.
apply: hom_space_boundedly_compact.
- have he : [set g : H | `|g - f| <= r] = closed_ball_ Num.norm f r.
    by apply/seteqP; split=> g /=; rewrite /closed_ball_ distrC.
  rewrite he; exact: closed_closed_ball_.
- exists (`|f| + r)=> g hg.
  have h := ler_normD (g - f) f.
  rewrite subrK in h; apply: (le_trans h); rewrite addrC lerD2l.
  exact: hg.
Qed.

(** Source for [hom_space_locally_compact]: "all norms on A(V, V)
    induce the same locally compact topology", Federer 2.7.16, p. 134:
    Hom(V, W) is locally compact; every member f has the compact closed
    neighbourhood {g : |g - f| <= 1}. Direct formalisation. *)
Theorem hom_space_locally_compact : locally_compact [set: H].
Proof.
move=> f _; rewrite withinET; exists [set g : H | `|g - f| <= 1].
  apply: (@filterS _ _ _ (ball f 1)); last exact: nbhsx_ballx.
  by move=> g; rewrite -ball_normE /= distrC=> h; exact: ltW.
split; first exact: hom_space_closed_ball_compact.
have he : [set g : H | `|g - f| <= 1] = closed_ball_ Num.norm f 1.
  by apply/seteqP; split=> g /=; rewrite /closed_ball_ distrC.
rewrite he; exact: closed_closed_ball_.
Qed.

(** Source for [hom_additive_lch_group]: "the topological assumptions
    of our general theory are satisfied", Federer 2.7.16, p. 134, for the
    additive group of Hom(V, W) used in example (2), p. 136: it is a
    locally compact Hausdorff topological group in the sense of 2.7.1,
    p. 121. Direct formalisation. *)
Theorem hom_additive_lch_group :
  is_locally_compact_hausdorff_group (fun f g : H => f + g) (fun f => - f) 0.
Proof.
split; first exact: hom_additive_topological_group.
- exact: hom_space_hausdorff.
- exact: hom_space_locally_compact.
Qed.

End HomSpace.
