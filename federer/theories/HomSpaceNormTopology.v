(** Federer (1969), 2.7.16, printed p. 134: "all norms on A(V, V) induce the
    same locally compact topology. In particular we can choose an inner
    product on V and norm Hom(V, V) as in 1.7.6." Here V and W carry inner
    products and finite bases, and Hom(V, W) carries the topology of the
    inner product of 1.7.9, p. 35, as in HomSpaceTopology.v. Every norm N on
    Hom(V, W) in the sense of 1.10.5, p. 48, induces this topology, by
    FiniteNormEquivalence.v and the base x |-> e_k*(x) w_i of Hom(V, W)
    (HomCompositionDeterminant.v, from 1.4.5, p. 21). The operator norm of
    1.7.6, p. 33, is such a norm, so the topology of Hom(V, W) is the one
    used by Federer for the estimates of composition and inversion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric LinearBasis InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology Hom HomInner HomCompositionDeterminant HomSpaceTopology HomeomorphismUP
  FiniteNormEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HomNorms.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable k : nat.
Variable c : 'I_k -> W.
Hypothesis hc : is_basis c.
Local Notation H := (inner_metric_space (hom_inner_productP hB hC hb)).

(** Source for [hom_space_finite_basis]: Hom(V, W) has the finite base
    x |-> e_i*(x) w_j, Federer 1.4.5, p. 21, so that "dim Hom(V, V) < oo"
    in 2.7.16, p. 134. Supporting lemma. *)
Lemma hom_space_finite_basis : exists m, exists u : 'I_m -> Hom V W, is_basis u.
Proof. by exists #|{: 'I_n * 'I_k}|, (hom_rank_one_base hb c); exact: hom_rank_one_baseP. Qed.

(** Source for [hom_space_norm_same_nbhs]: "all norms ... induce the
    same ... topology. In particular we can choose an inner product on V
    and norm Hom(V, V) as in 1.7.6", Federer 2.7.16, p. 134: a set S is a
    neighbourhood of f in Hom(V, W) with the topology of 1.7.9 if and
    only if it is a neighbourhood of f for the metric of any norm N.
    Direct formalisation. *)
Theorem hom_space_norm_same_nbhs (N : Hom V W -> R) (hN : is_real_norm N) (f : Hom V W)
    (S : set (Hom V W)) :
  nbhs (f : H) S <-> nbhs (f : real_norm_metric_space hN) S.
Proof.
exact: (finite_norm_inner_same_nbhs (hom_inner_productP hB hC hb) (hom_rank_one_baseP hb hc) hN).
Qed.

(** Source for [hom_space_norm_homeomorphism]: Federer 2.7.16, p. 134:
    the identity of Hom(V, W) is a homeomorphism of the topology of 1.7.9
    onto the topology of any norm, in the sense of 2.7.1, p. 121.
    Supporting lemma. *)
Lemma hom_space_norm_homeomorphism (N : Hom V W -> R) (hN : is_real_norm N) :
  is_homeomorphism_with_inverse (fun f : H => (f : real_norm_metric_space hN))
    (fun f : real_norm_metric_space hN => (f : H)).
Proof. exact: (finite_norm_inner_homeomorphism (hom_inner_productP hB hC hb) (hom_rank_one_baseP hb hc)). Qed.

(** Source for [hom_space_norm_locally_compact]: "all norms on A(V, V)
    induce the same locally compact topology", Federer 2.7.16, p. 134,
    for Hom(V, W): the topology of any norm is locally compact. Direct
    formalisation. *)
Theorem hom_space_norm_locally_compact (N : Hom V W -> R) (hN : is_real_norm N) :
  locally_compact [set: real_norm_metric_space hN].
Proof. exact: (@finite_norm_locally_compact R (Hom V W) _ _ (hom_rank_one_baseP hb hc) N hN). Qed.

(** Source for [hom_operator_norm_real_norm]: the operator norm
    ||f|| = sup{|f(x)| : |x| <= 1} of 1.7.6, p. 33, is a norm on
    Hom(V, W) ("norm Hom(V, V) as in 1.7.6", Federer 2.7.16, p. 134);
    definiteness follows from |f| <= (dim V)^{1/2} ||f||, 1.7.9, p. 35.
    Supporting lemma. *)
Lemma hom_operator_norm_real_norm : is_real_norm (hom_operator_norm hB hC hb).
Proof.
split; first split.
- exact: hom_operator_norm_nonnegative.
- move=> a f; apply/eqP; rewrite eq_le; apply/andP; split.
    apply: hom_operator_norm_least.
      by rewrite mulr_ge0 ?normr_ge0 ?hom_operator_norm_nonnegative.
    move=> x; have -> : (a *: f) x = a *: f x by [].
    by rewrite inner_normZ -mulrA ler_wpM2l ?normr_ge0 ?hom_operator_norm_bound.
  have [->|ha] := eqVneq a 0.
    by rewrite normr0 mul0r hom_operator_norm_nonnegative.
  have hpos : 0 < `|a| by rewrite normr_gt0.
  have hle : hom_operator_norm hB hC hb f <= `|a|^-1 * hom_operator_norm hB hC hb (a *: f).
    apply: hom_operator_norm_least.
      by rewrite mulr_ge0 ?invr_ge0 ?normr_ge0 ?hom_operator_norm_nonnegative.
    move=> x; have -> : f x = a^-1 *: (a *: f) x.
      by have -> : (a *: f) x = a *: f x by []; rewrite scalerA mulVf ?scale1r.
    rewrite inner_normZ normfV -mulrA ler_wpM2l ?invr_ge0 ?normr_ge0 //.
    exact: hom_operator_norm_bound.
  have h := ler_wpM2l (ltW hpos) hle.
  by rewrite mulrA mulfV ?gt_eqF // mul1r in h.
- exact: hom_operator_norm_add.
- move=> f hf; apply/eqP; rewrite -(inner_norm_eq0 (hom_inner_productP hB hC hb)).
  rewrite eq_le inner_norm_nonnegative andbT.
  have h := hom_space_le_operator (f : H).
  by rewrite hf mulr0 in h.
Qed.

(** Source for [hom_operator_norm_same_nbhs]: "we can choose an inner
    product on V and norm Hom(V, V) as in 1.7.6", Federer 2.7.16, p. 134:
    the metric ||g - f|| of the operator norm induces the topology of
    Hom(V, W). Direct formalisation, as an instance of
    hom_space_norm_same_nbhs; hom_space_nbhs_operator of
    HomSpaceTopology.v is the same statement through balls. *)
Theorem hom_operator_norm_same_nbhs (f : Hom V W) (S : set (Hom V W)) :
  nbhs (f : H) S <-> nbhs (f : real_norm_metric_space hom_operator_norm_real_norm) S.
Proof. exact: hom_space_norm_same_nbhs. Qed.

End HomNorms.
