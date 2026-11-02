(** Federer (1969), 2.7.12, printed p. 129: "Weil's condition holds whenever
    chi is positive and the isotropy group G^x is compact, because every
    continuous homomorphism of a compact group into the multiplicative group
    of positive numbers is constant with value 1." This file proves the
    quoted fact about compact groups. A group is given by is_group_laws
    (TopologicalGroupUP.v); it is compact when [set: G] is compact. No
    continuity of the group operations is used. Federer gives no argument.
    The proof here: a continuous real function on a compact space is
    bounded; if phi(g) > 1, then phi(g^n) = phi(g)^n >= 1 + n (phi(g) - 1)
    is unbounded, and if phi(g) < 1, then phi(g^{-1}) > 1. The local erratum
    has no entry for p. 129. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground TopologicalGroupUP TopologicalGroupLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_bernoulli_inequality]: the estimate
    (1 + r)^n >= 1 + n r for r >= 0, supporting the proof of "every
    continuous homomorphism of a compact group into the multiplicative
    group of positive numbers is constant with value 1", Federer 2.7.12,
    p. 129. Supporting lemma, by induction on n. *)
Lemma real_bernoulli_inequality (R : realType) (r : R) n : 0 <= r -> 1 + n%:R * r <= (1 + r) ^+ n.
Proof.
move=> hr; elim: n=> [|n ih]; first by rewrite mul0r addr0 expr0.
rewrite exprSr -natr1.
have hn : 0 <= n%:R :> R := ler0n _ _.
have h1 : (1 + n%:R * r) * (1 + r) <= (1 + r) ^+ n * (1 + r).
  by apply: ler_wpM2r=> //; lra.
apply: le_trans h1; nra.
Qed.

Section CompactGroupCharacters.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_group_laws mul inv e.
Variable phi : G -> R.
Hypothesis hphic : continuous (phi : G -> real_line_metric R).
Hypothesis hphiM : forall g h, phi (mul g h) = phi g * phi h.
Hypothesis hphip : forall g, 0 < phi g.

(** Source for [positive_character_unit]: phi(e) = 1 for a
    homomorphism phi of G into the multiplicative group of positive
    numbers, as in Federer 2.7.12, p. 129. Supporting lemma. *)
Lemma positive_character_unit : phi e = 1.
Proof.
have h := hphiM e e; rewrite (group_mul1g hG) -{1}[phi e]mulr1 in h.
exact: esym (mulfI (lt0r_neq0 (hphip e)) h).
Qed.

(** Source for [positive_character_inverse]: phi(g^{-1}) = phi(g)^{-1}
    for a homomorphism phi into the positive numbers, Federer 2.7.12,
    p. 129. Supporting lemma. *)
Lemma positive_character_inverse g : phi (inv g) = (phi g)^-1.
Proof.
apply: (mulIf (lt0r_neq0 (hphip g))).
by rewrite -hphiM (group_mulVg hG) positive_character_unit (mulVf (lt0r_neq0 (hphip g))).
Qed.

(** Source for [positive_character_power]: phi(g^n) = phi(g)^n, with
    g^n = g ... g (n factors) and g^0 = e, supporting Federer 2.7.12,
    p. 129. Supporting lemma, by induction on n. *)
Lemma positive_character_power g n : phi (iter n (mul g) e) = phi g ^+ n.
Proof.
elim: n=> [|n ih]; first by rewrite expr0 /= positive_character_unit.
by rewrite iterS hphiM ih exprS.
Qed.

(** Source for [compact_positive_character_bounded]: a continuous real
    function on a compact group is bounded above, supporting "every
    continuous homomorphism of a compact group into the multiplicative
    group of positive numbers is constant with value 1", Federer 2.7.12,
    p. 129. The image of [set: G] under phi is a compact set of real
    numbers. Supporting lemma. *)
Lemma compact_positive_character_bounded : compact [set: G] -> exists B : R, forall g, phi g <= B.
Proof.
move=> hc.
have hK : compact (phi @` [set: G] : set (real_line_metric R)).
  by apply: continuous_compact hc; exact: continuous_subspaceT.
have hK' : compact (phi @` [set: G] : set R^o) := hK.
have [B hB] := @filter_ex _ _ proper_pinfty_nbhs _ (compact_bounded hK').
exists B=> g; apply: le_trans (ler_norm _) _; apply: hB; exact: imageT.
Qed.

(** Source for [compact_group_positive_character_unit]: "every
    continuous homomorphism of a compact group into the multiplicative
    group of positive numbers is constant with value 1", Federer 2.7.12,
    p. 129. Direct formalisation; the proof is not printed. *)
Theorem compact_group_positive_character_unit : compact [set: G] -> forall g, phi g = 1.
Proof.
move=> hc; have [B hB] := compact_positive_character_bounded hc.
have hle g : phi g <= 1.
  rewrite leNgt; apply/negP=> hg1.
  pose r := phi g - 1.
  have hr : 0 < r by rewrite /r subr_gt0.
  have hBr : 0 <= `|B| / r by apply: divr_ge0; [exact: normr_ge0|exact: ltW].
  pose n := Num.Def.archi_bound (`|B| / r).
  have hn : `|B| / r < n%:R := archi_boundP hBr.
  have hnr : `|B| < n%:R * r by rewrite -ltr_pdivrMr.
  have hpow := real_bernoulli_inequality n (ltW hr).
  have he : 1 + r = phi g by rewrite /r addrC subrK.
  rewrite he -positive_character_power in hpow.
  have := hB (iter n (mul g) e); have := ler_norm B; lra.
move=> g; apply/eqP; rewrite eq_le hle /=.
by have := hle (inv g); rewrite positive_character_inverse invf_le1.
Qed.

End CompactGroupCharacters.
