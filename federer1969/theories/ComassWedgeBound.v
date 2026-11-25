(** Federer (1969), 1.8.1, p. 39: comass of a wedge is at most
    binomial(p+q,p) times the two comasses. The proof uses the shuffle
    identity of 1.4.2, p. 18 *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerNorm ExteriorGrading
  FiniteExteriorPowers AlternatingCoordinates AlternatingPairing CovectorProducts
  AlternatingProduct AlternatingShuffle Shuffles ExteriorPermutation
  SimpleUnitFactors ComassUP ComassTupleBounds ShuffleCardinalityBound Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [comass_wedge_bound]: Federer 1.8.1,
    p. 39, the general comass exterior-product bound. Each shuffle
    contributes at most the product of the two comasses; the first
    block determines the shuffle, giving the binomial bound. *)
Theorem comass_wedge_bound (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    p q (hp : (0 < p)%N) (hq : (0 < q)%N)
    (phi : A_m V R^o p) (psi : A_m V R^o q) a b c :
  is_comass h2 hB phi a -> is_comass h2 hB psi b ->
  is_comass h2 hB (form_wedge h2 (scalar_bilinear R) phi psi) c ->
  c <= 'C(p+q,p)%:R * (a*b).
Proof.
move=> ha hb hc.
have hpq : (0 < p+q)%N := leq_trans hp (leq_addr q p).
have ha0 := @comass_nonnegative R h2 V B hB p phi a hp ha.
have hb0 := @comass_nonnegative R h2 V B hB q psi b hq hb.
apply: (@comass_least_upper_bound R h2 V B hB (p+q)
  (form_wedge h2 (scalar_bilinear R) phi psi) c hc _) => x hx.
have [u [hu ->]] := @simple_unit_ball_factors R h2 V B hB (p+q) hpq x hx.
rewrite pairing_e_lambda form_wedge_shuffle.
pose t : (p+q).-tuple V := [tuple of map u (ord_tuple (p+q))].
have ht i : inner_norm hB (tnth t i) <= 1 by rewrite /t tnth_map tnth_ord_tuple; exact: hu.
have hl s : `|phi (shuffle_left_tuple t (val s))| <= a.
  apply: (@comass_unit_tuple_bound R h2 V B hB p hp phi a ha).
  exact: shuffle_left_unit_factors ht.
have hr s : `|psi (shuffle_right_tuple t (val s))| <= b.
  apply: (@comass_unit_tuple_bound R h2 V B hB q hq psi b hb).
  exact: shuffle_right_unit_factors ht.
have hterm (s : Sh p q) :
    `|FedererPermutation.index R (val s) *
      (phi (shuffle_left_tuple t (val s))*psi (shuffle_right_tuple t (val s)))| <= a*b.
  rewrite normrM /FedererPermutation.index normrX normrN normr1 expr1n mul1r normrM.
  apply: ler_pM; try exact: normr_ge0.
  - exact: hl.
  - exact: hr.
have hs : (\sum_(s : Sh p q)
    `|FedererPermutation.index R (val s) *
      (phi (shuffle_left_tuple t (val s))*psi (shuffle_right_tuple t (val s)))|)
      <= #|{: Sh p q}|%:R * (a*b).
  have hconst : (\sum_(s : Sh p q) (a*b)) = #|{: Sh p q}|%:R * (a*b).
    by rewrite sumr_const mulr_natl.
  rewrite -hconst; apply: ler_sum => s _; exact: hterm.
apply: (le_trans (ler_norm _)); apply: (le_trans (ler_norm_sum _ _ _)).
apply: (le_trans hs).
apply: ler_wpM2r; first exact: mulr_ge0.
by rewrite ler_nat; exact: shuffle_cardinality_bound.
Qed.
