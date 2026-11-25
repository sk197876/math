(** Federer (1969), 2.7.14, printed pp. 132–133: in the proof of the
    theorem, "because Delta_G and chi map the compact subgroup S onto {1}".
    This rests on the fact stated in 2.7.12, p. 129: "every continuous
    homomorphism of a compact group into the multiplicative group of
    positive numbers is constant with value 1". The fact is proved here for
    a compact subgroup S of a group G and a continuous positive
    multiplicative function phi on G, without forming S as a topological
    group. Federer gives no argument. The proof: phi(S) is a compact set of
    real numbers, hence bounded; if phi(s) > 1 for some s in S, then
    phi(s^n) = phi(s)^n >= 1 + n (phi(s) - 1) is unbounded, although s^n
    belongs to S; if phi(s) < 1, then phi(s^{-1}) > 1; the estimate is
    real_bernoulli_inequality of CompactGroupCharacters.v (2.7.12). The
    theorem compact_group_positive_character_unit of that file treats a
    compact group [set: G]; the present form for a compact subgroup of a
    group which need not be compact is the one used in 2.7.14. No continuity
    of the group operations is used. The local erratum has no entry for
    this argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground TopologicalGroupUP TopologicalGroupLaws CompactGroupCharacters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactSubgroupCharacter.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_group_laws mul inv e.
Variable S : set G.
Hypothesis hS : is_subgroup mul inv e S.
Variable phi : G -> R.
Hypothesis hphic : continuous (phi : G -> real_line_metric R).
Hypothesis hphiM : forall g h, phi (mul g h) = phi g * phi h.
Hypothesis hphip : forall g, 0 < phi g.

(** Source for [subgroup_character_unit]: phi(e) = 1 for a homomorphism
    phi into the multiplicative group of positive numbers, supporting
    Federer 2.7.14, p. 133. Supporting lemma. *)
Lemma subgroup_character_unit : phi e = 1.
Proof.
have h := hphiM e e; rewrite (group_mul1g hG) -{1}[phi e]mulr1 in h.
exact: esym (mulfI (lt0r_neq0 (hphip e)) h).
Qed.

(** Source for [subgroup_character_inverse]: phi(g^{-1}) = phi(g)^{-1},
    supporting Federer 2.7.14, p. 133. Supporting lemma. *)
Lemma subgroup_character_inverse g : phi (inv g) = (phi g)^-1.
Proof.
apply: (mulIf (lt0r_neq0 (hphip g))).
by rewrite -hphiM (group_mulVg hG) subgroup_character_unit (mulVf (lt0r_neq0 (hphip g))).
Qed.

(** Source for [subgroup_character_power]: phi(g^n) = phi(g)^n, with
    g^n = g ... g (n factors) and g^0 = e, supporting Federer 2.7.14,
    p. 133. Supporting lemma, by induction on n. *)
Lemma subgroup_character_power g n : phi (iter n (mul g) e) = phi g ^+ n.
Proof.
elim: n=> [|n ih]; first by rewrite expr0 /= subgroup_character_unit.
by rewrite iterS hphiM ih exprS.
Qed.

(** Source for [subgroup_power_member]: the powers s^n of a member s
    of the subgroup S belong to S, supporting Federer 2.7.14, p. 133.
    Supporting lemma, by induction on n. *)
Lemma subgroup_power_member s n : S s -> S (iter n (mul s) e).
Proof.
move=> hs; elim: n=> [|n ih]; first exact: subgroup_unit hS.
by rewrite iterS; exact: (subgroup_mul hS hs ih).
Qed.

(** Source for [compact_subgroup_character_bounded]: a continuous real
    function is bounded above on the compact set S, supporting "Delta_G
    and chi map the compact subgroup S onto {1}", Federer 2.7.14, p. 133.
    The image of S under phi is a compact set of real numbers.
    Supporting lemma. *)
Lemma compact_subgroup_character_bounded : compact S -> exists B : R, forall s, S s -> phi s <= B.
Proof.
move=> hc.
have hK : compact (phi @` S : set (real_line_metric R)).
  apply: (@continuous_compact G (real_line_metric R) phi S) hc.
  exact: (@continuous_subspaceT G (real_line_metric R) S phi hphic).
have hK' : compact (phi @` S : set R^o) := hK.
have [B hB] := @filter_ex _ _ proper_pinfty_nbhs _ (compact_bounded hK').
exists B=> s hs; apply: le_trans (ler_norm _) _; apply: hB; exact: imageP.
Qed.

(** Source for [compact_subgroup_positive_character_unit]: "Delta_G and
    chi map the compact subgroup S onto {1}", Federer 2.7.14, p. 133,
    from the fact quoted in 2.7.12, p. 129, that "every continuous
    homomorphism of a compact group into the multiplicative group of
    positive numbers is constant with value 1". Direct formalisation for
    a compact subgroup S of G and a continuous positive multiplicative
    function phi on G; local proof, since Federer prints none. *)
Theorem compact_subgroup_positive_character_unit : compact S -> forall s, S s -> phi s = 1.
Proof.
move=> hc; have [B hB] := compact_subgroup_character_bounded hc.
have hle s : S s -> phi s <= 1.
  move=> hs; rewrite leNgt; apply/negP=> hs1.
  pose r := phi s - 1.
  have hr : 0 < r by rewrite /r subr_gt0.
  have hBr : 0 <= `|B| / r by apply: divr_ge0; [exact: normr_ge0|exact: ltW].
  pose n := Num.Def.archi_bound (`|B| / r).
  have hn : `|B| / r < n%:R := archi_boundP hBr.
  have hnr : `|B| < n%:R * r by rewrite -ltr_pdivrMr.
  have hpow := real_bernoulli_inequality n (ltW hr).
  have he : 1 + r = phi s by rewrite /r addrC subrK.
  rewrite he -subgroup_character_power in hpow.
  have := hB (iter n (mul s) e) (subgroup_power_member n hs); have := ler_norm B; lra.
move=> s hs; apply/eqP; rewrite eq_le (hle s hs) /=.
by have := hle (inv s) (subgroup_inv hS hs); rewrite subgroup_character_inverse invf_le1.
Qed.

End CompactSubgroupCharacter.
