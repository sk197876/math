(** Federer (1969), 1.8.1, pp. 38-39: supporting tuple estimates for comass
    and its shuffle product bound. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerNorm ExteriorGrading
  FiniteExteriorPowers AlternatingCoordinates AlternatingPairing CovectorProducts
  SimpleElementary SimpleUnitFactors ComassUP ComassBounds AlternatingShuffle Shuffles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Tuples.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [comass_unit_tuple_bound]: Federer 1.8.1, p. 38, equivalent
    evaluation bound on unit-ball factors. *)
Lemma comass_unit_tuple_bound m (hm : (0 < m)%N)
    (phi : A_m V R^o m) c (hc : is_comass h2 hB phi c) (t : m.-tuple V) :
  (forall i, inner_norm hB (tnth t i) <= 1) -> `|phi t| <= c.
Proof.
move=> ht.
have hs := @unit_factors_simple_unit_ball R h2 V B hB m (tnth t) ht.
have hh := @comass_absolute_unit_bound R h2 V B hB m hm phi c hc
  (e_lambda (tnth t) (ord_tuple m)) hs.
rewrite -tuple_product pairing_e_lambda in hh.
have he : [tuple of map idfun t] = t by apply: val_inj; rewrite /= map_id.
by rewrite he in hh.
Qed.

(** Source for [shuffle_left_unit_factors]: Federer 1.8.1,
    p. 39, supporting shuffle estimate: selecting and permuting
    the first p factors preserves their unit-ball bounds. *)
Lemma shuffle_left_unit_factors p q (t : (p+q).-tuple V) (s : 'S_(p+q)) :
  (forall i, inner_norm hB (tnth t i) <= 1) ->
  forall i, inner_norm hB (tnth (shuffle_left_tuple t s) i) <= 1.
Proof.
move=> ht i.
have hmem := mem_tnth i (shuffle_left_tuple t s).
case/mapP: hmem => j hj ->.
have hj' := mem_take hj.
case/mapP: hj' => k hk ->.
by rewrite -tnth_nth; exact: ht.
Qed.

(** Source for [shuffle_right_unit_factors]: Federer 1.8.1,
    p. 39, supporting shuffle estimate for the last q factors. *)
Lemma shuffle_right_unit_factors p q (t : (p+q).-tuple V) (s : 'S_(p+q)) :
  (forall i, inner_norm hB (tnth t i) <= 1) ->
  forall i, inner_norm hB (tnth (shuffle_right_tuple t s) i) <= 1.
Proof.
move=> ht i.
have hmem := mem_tnth i (shuffle_right_tuple t s).
case/mapP: hmem => j hj ->.
have hj' := mem_drop hj.
case/mapP: hj' => k hk ->.
by rewrite -tnth_nth; exact: ht.
Qed.
End Tuples.
