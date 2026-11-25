(** Federer (1969), 2.7.16, printed pp. 133–134: "If dim V < oo, then dim
    A(V, V) < oo and all norms on A(V, V) induce the same locally compact
    topology." This module proves the general fact behind the second
    assertion: on a vector space V with a finite basis any two norms N_1,
    N_2 in the sense of 1.10.5, p. 48 (is_real_norm) satisfy c N_1 <= N_2 <=
    C N_1 with 0 < c and 0 < C, hence the metrics N_1(x - y) and N_2(x - y)
    of 2.2.7, p. 64 (real_norm_metric_space) have the same neighbourhoods,
    and this topology is Hausdorff and locally compact. Federer gives no
    proof. The proof chooses an inner product for which the given basis is
    orthonormal; every norm is bounded by a multiple of the inner product
    norm by the expansion in the basis and Cauchy's inequality
    (FiniteNormUpperBound.v), and the inner product norm is bounded by a
    multiple of every norm because a norm attains a positive minimum on the
    compact unit sphere of the inner product (FiniteNormLowerBound.v, by
    1.7.1, p. 28). The closed balls are compact by
    FiniteNormMetricCompactness.v. The topology of an inner product (1.7.1,
    p. 28, inner_metric_space) is the topology of its norm, so every norm on
    a space with an inner product and a finite basis induces the topology of
    the inner product. MathComp-analysis 1.16 contains no theorem on the
    equivalence of norms in finite dimension for an abstract lmodType, so
    none is reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LinearBasis InnerProductUP InnerNorm InnerMetric
  FiniteBasisInnerWitness FiniteNormUpperBound FiniteNormLowerBound FiniteNormMetricCompactness
  NormClosureLaws HilbertFormCompactness HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormComparison.
Variable R : realType.
Variable V : lmodType R.
Variables N1 N2 : V -> R.
Hypothesis h1 : is_real_norm N1.
Hypothesis h2 : is_real_norm N2.
Local Notation M1 := (real_norm_metric_space h1).
Local Notation M2 := (real_norm_metric_space h2).

(** Source for [real_norm_bound_nbhs]: supporting Federer 2.7.16,
    p. 134, "all norms ... induce the same ... topology": if
    N_2 <= C N_1 with 0 < C, then every neighbourhood of x for the metric
    of N_2 is a neighbourhood of x for the metric of N_1. Supporting
    lemma. *)
Lemma real_norm_bound_nbhs (C : R) : 0 < C -> (forall x, N2 x <= C * N1 x) ->
  forall (x : V) (S : set V), nbhs (x : M2) S -> nbhs (x : M1) S.
Proof.
move=> hC hb x S /(metricType_numDomainType.nbhs_mdistP (x : M2) S) [e he hS].
apply/(metricType_numDomainType.nbhs_mdistP (x : M1) S).
exists (e / C); first by rewrite /= divr_gt0.
move=> y /= hy; apply: hS.
change (is_true (N2 (x - y) < e)); change (is_true (N1 (x - y) < e / C)) in hy.
apply: le_lt_trans (hb (x - y)) _.
by rewrite mulrC -ltr_pdivlMr.
Qed.

Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [finite_norm_comparison]: Federer 2.7.16, p. 134, "all
    norms on A(V, V) induce the same ... topology", for any space with a
    finite basis: N_2 <= C N_1 for some C > 0. Supplied proof, through an
    auxiliary inner product for which e is orthonormal (1.7.1, p. 28). *)
Theorem finite_norm_comparison : exists2 C : R, 0 < C & forall x, N2 x <= C * N1 x.
Proof.
have [B [hB ho]] := finite_basis_inner_product_witness he.
have hu := @finite_seminorm_inner_upper_bound R V B hB N2 h2.1 n e he ho.
have [c [hc hl]] := @finite_norm_inner_lower_bound R V B hB N1 h1 n e he.
pose S := \sum_i N2 (e i).
have hS : 0 <= S by apply: sumr_ge0=> i _; exact: real_seminorm_nonnegative h2.1 _.
exists ((S + 1) * c); first by rewrite mulr_gt0 // ltr_wpDl.
move=> x; apply: le_trans (hu x) _.
apply: (@le_trans _ _ ((S + 1) * inner_norm hB x)).
  by rewrite ler_wpM2r ?inner_norm_nonnegative // lerDl.
by rewrite -mulrA ler_wpM2l ?(hl x) // addr_ge0.
Qed.

End NormComparison.

Section FiniteNorms.
Variable R : realType.
Variable V : lmodType R.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [finite_norms_equivalent]: Federer 2.7.16, p. 134, "all
    norms on A(V, V) induce the same locally compact topology", for any
    space with a finite basis: c N_1 <= N_2 <= C N_1 for some c > 0 and
    C > 0. Supplied proof of the comparison underlying Federer's
    assertion. *)
Theorem finite_norms_equivalent (N1 N2 : V -> R) : is_real_norm N1 -> is_real_norm N2 ->
  exists c C : R, [/\ 0 < c, 0 < C & forall x, c * N1 x <= N2 x /\ N2 x <= C * N1 x].
Proof.
move=> h1 h2.
have [C hC hu] := finite_norm_comparison h1 h2 he.
have [D hD hl] := finite_norm_comparison h2 h1 he.
exists D^-1, C; split; rewrite ?invr_gt0 // => x; split; last exact: hu.
by rewrite mulrC ler_pdivrMr // mulrC; exact: hl.
Qed.

(** Source for [finite_norms_same_nbhs]: "all norms on A(V, V) induce
    the same ... topology", Federer 2.7.16, p. 134, for any space with a
    finite basis: a set S is a neighbourhood of x for the metric of N_1
    if and only if it is one for the metric of N_2. Direct formalisation
    of the general statement. *)
Theorem finite_norms_same_nbhs (N1 N2 : V -> R) (h1 : is_real_norm N1) (h2 : is_real_norm N2)
    (x : V) (S : set V) :
  nbhs (x : real_norm_metric_space h1) S <-> nbhs (x : real_norm_metric_space h2) S.
Proof.
have [C hC hu] := finite_norm_comparison h1 h2 he.
have [D hD hl] := finite_norm_comparison h2 h1 he.
by split; [exact: real_norm_bound_nbhs hl x S|exact: real_norm_bound_nbhs hu x S].
Qed.

(** Source for [finite_norms_same_open]: Federer 2.7.16, p. 134, "all
    norms ... induce the same ... topology": the open sets of the two
    metrics coincide. Supporting lemma. *)
Lemma finite_norms_same_open (N1 N2 : V -> R) (h1 : is_real_norm N1) (h2 : is_real_norm N2)
    (S : set V) :
  open (S : set (real_norm_metric_space h1)) <-> open (S : set (real_norm_metric_space h2)).
Proof.
rewrite !openE /interior; split=> hS x hx.
- by apply/(finite_norms_same_nbhs h1 h2); exact: hS.
- by apply/(finite_norms_same_nbhs h1 h2); exact: hS.
Qed.

(** Source for [finite_norms_identity_homeomorphism]: Federer 2.7.16,
    p. 134, "all norms ... induce the same ... topology": the identity
    map of V is a homeomorphism between the two metric spaces, in the
    sense of 2.7.1, p. 121. Supporting lemma. *)
Lemma finite_norms_identity_homeomorphism (N1 N2 : V -> R) (h1 : is_real_norm N1)
    (h2 : is_real_norm N2) :
  is_homeomorphism_with_inverse (fun x : real_norm_metric_space h1 => (x : real_norm_metric_space h2))
    (fun x : real_norm_metric_space h2 => (x : real_norm_metric_space h1)).
Proof.
split=> // x S hS.
- exact/(finite_norms_same_nbhs h1 h2).
- exact/(finite_norms_same_nbhs h1 h2).
Qed.

Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [finite_norm_hausdorff]: the topology induced by a norm
    is Hausdorff, being a metric topology (2.2.7, p. 64); supporting
    Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma finite_norm_hausdorff : hausdorff_space M.
Proof. exact: (@metric_hausdorff R [the metricType R of M]). Qed.

(** Source for [finite_norm_closed_ball_compact]: the closed balls
    {y : N(y - x) <= r} are compact for a norm N on a space with a finite
    basis, by 1.7.1, p. 28; supporting Federer 2.7.16, p. 134. The ball
    is the image of {y : N(y) <= r} under the translation y |-> x + y.
    Supporting lemma. *)
Lemma finite_norm_closed_ball_compact (x : M) (r : R) : compact [set y : M | N (y - x) <= r].
Proof.
have hK := @finite_norm_metric_ball_compact R V N hN n e he r.
have -> : [set y : M | N (y - x) <= r] = (fun y : M => (x + y : M)) @` [set y : M | N y <= r].
  apply/seteqP; split=> y hy.
  - by exists (y - x); [exact: hy|rewrite addrC subrK].
  - by have [z hz <-] := hy; rewrite /= addrC addKr.
apply: continuous_compact hK; apply: continuous_subspaceT=> y.
exact: real_norm_metric_translate_continuous.
Qed.

(** Source for [finite_norm_locally_compact]: "all norms on A(V, V)
    induce the same locally compact topology", Federer 2.7.16, p. 134,
    for any space with a finite basis: the topology of a norm is locally
    compact; every x has the compact closed neighbourhood
    {y : N(y - x) <= 1}. Direct formalisation of the general statement. *)
Theorem finite_norm_locally_compact : locally_compact [set: M].
Proof.
move=> x _; rewrite withinET; exists [set y : M | N (y - x) <= 1].
  apply/(metricType_numDomainType.nbhs_mdistP x); exists 1=> [|y /= hy]; first exact: ltr01.
  change (is_true (N (x - y) < 1)) in hy.
  by rewrite (real_seminorm_subtract hN.1); exact: ltW.
split; first exact: finite_norm_closed_ball_compact.
apply: compact_closed; first exact: finite_norm_hausdorff.
exact: finite_norm_closed_ball_compact.
Qed.

End FiniteNorms.

Section InnerNorms.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation VT := (inner_metric_space hB).

(** Source for [inner_real_norm_same_nbhs]: the topology of an inner
    product, 1.7.1, p. 28, is the topology of its norm |x| regarded as a
    norm in the sense of 1.10.5, p. 48; supporting Federer 2.7.16, p. 134,
    "we can choose an inner product on V". Both metrics are |x - y|.
    Supporting lemma. *)
Lemma inner_real_norm_same_nbhs (x : V) (S : set V) :
  nbhs (x : VT) S <-> nbhs (x : real_norm_metric_space (inner_norm_real_norm hB)) S.
Proof.
split.
- move=> /(metricType_numDomainType.nbhs_mdistP (x : VT) S) [r hr hS].
  apply/(metricType_numDomainType.nbhs_mdistP (x : real_norm_metric_space (inner_norm_real_norm hB)) S).
  by exists r=> // y hy; exact: hS.
- move=> /(metricType_numDomainType.nbhs_mdistP (x : real_norm_metric_space (inner_norm_real_norm hB)) S).
  move=> [r hr hS]; apply/(metricType_numDomainType.nbhs_mdistP (x : VT) S).
  by exists r=> // y hy; exact: hS.
Qed.

Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [finite_norm_inner_same_nbhs]: Federer 2.7.16, p. 134,
    "all norms ... induce the same ... topology. In particular we can
    choose an inner product on V": on a space with an inner product and a
    finite basis, every norm N induces the topology of the inner product.
    Direct formalisation. *)
Theorem finite_norm_inner_same_nbhs (N : V -> R) (hN : is_real_norm N) (x : V) (S : set V) :
  nbhs (x : VT) S <-> nbhs (x : real_norm_metric_space hN) S.
Proof.
rewrite inner_real_norm_same_nbhs.
exact: (finite_norms_same_nbhs hb (inner_norm_real_norm hB) hN).
Qed.

(** Source for [finite_norm_inner_homeomorphism]: Federer 2.7.16,
    p. 134: the identity map of V is a homeomorphism of V with the
    topology of the inner product onto V with the topology of a norm N,
    in the sense of 2.7.1, p. 121. Supporting lemma. *)
Lemma finite_norm_inner_homeomorphism (N : V -> R) (hN : is_real_norm N) :
  is_homeomorphism_with_inverse (fun x : VT => (x : real_norm_metric_space hN))
    (fun x : real_norm_metric_space hN => (x : VT)).
Proof.
split=> // x S hS.
- exact/(finite_norm_inner_same_nbhs hN).
- exact/(finite_norm_inner_same_nbhs hN).
Qed.

End InnerNorms.
