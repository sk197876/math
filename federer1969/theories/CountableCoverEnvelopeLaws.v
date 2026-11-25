(** Federer (1969), 2.10.1, p. 170: the preliminary covering infimum
    measures the whole space. We prove the fixed-family indexed form, used
    in the local counterexample for 2.3.8, p. 78. Source context:
    CountableCoverEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumAdd NonnegativeSumCover
  CountableGeometricBudget CountableCoverEnvelopeUP CountableCoverEnvelopeBasic MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_cover_envelope_is_measure]: direct fixed-family
    measure assertion in Federer 2.10.1, p. 170, without any diameter
    restriction; supporting the 2.3.8 counterexample. *)
Theorem countable_cover_envelope_is_measure (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (nu : set X -> \bar R)
    (hn : is_countable_cover_envelope S cost nu) :
  (forall j, 0 <= cost j) -> is_measure nu.
Proof.
move=> hcost; constructor; first exact: countable_cover_envelope_nonnegative hn.
move=> A F hF hc.
have hsum0 : 0 <= nonnegative_sum F nu := nonnegative_sum_nonnegative F nu.
case hs: (nonnegative_sum F nu)=> [r| |]; last by move: hsum0; rewrite hs.
2: exact: leey.
apply/lee_addgt0Pr=> e he.
have [b [hb hbsum]] := @countable_geometric_error_budget R (set X) F e hF he.
have happ B : exists G : set J, F B -> countable G /\
    B `<=` \bigcup_(j in G) S j /\ nonnegative_sum G cost < nu B + (b B)%:E.
  case: (pselect (F B))=> hB; last by exists set0.
  have hlt : nu B < +oo.
    apply: le_lt_trans (@nonnegative_sum_term R (set X) F nu B hB) _.
    by rewrite hs ltry.
  have hfin : nu B \is a fin_num.
    have hnon := @countable_cover_envelope_nonnegative R X J S cost nu hn B.
    by rewrite ge0_fin_numE.
  have hap : nu B < nu B + (b B)%:E.
    by rewrite -(fineK hfin) -EFinD lte_fin ltrDl hb.
  have [G hG] := @countable_cover_envelope_approximation R X J S cost nu hn B _ hap.
  by exists G.
pose G B := projT1 (cid (happ B)).
have hG B : F B -> countable (G B) /\ B `<=` \bigcup_(j in G B) S j /\
    nonnegative_sum (G B) cost < nu B + (b B)%:E := projT2 (cid (happ B)).
pose U := \bigcup_(B in F) G B.
have hU : countable U.
  apply: bigcup_countable hF _=> B hB; exact: (hG B hB).1.
have hAU : A `<=` \bigcup_(j in U) S j.
  move=> x hx; have [B hB hxB] := hc x hx.
  have [j hj hxj] := (hG B hB).2.1 x hxB; exists j=> //; by exists B.
apply: le_trans (@countable_cover_envelope_lower R X J S cost nu hn A U hU hAU) _.
have hu : nonnegative_sum U cost <= nonnegative_sum F (fun B => nonnegative_sum (G B) cost).
  apply: nonnegative_sum_cover hcost _; by move=> j hj.
apply: le_trans hu _.
have hmono : nonnegative_sum F (fun B => nonnegative_sum (G B) cost) <=
    nonnegative_sum F (fun B => nu B + (b B)%:E).
  apply: nonnegative_sum_mono=> B hB; exact: ltW (hG B hB).2.2.
apply: le_trans hmono _.
have hnu B (hB : F B) : 0 <= nu B := @countable_cover_envelope_nonnegative R X J S cost nu hn B.
have hb0 B (hB : F B) : 0 <= (b B)%:E := ltW (hb B).
rewrite (@nonnegative_sum_add R (set X) F nu (fun B => (b B)%:E) hnu hb0) hs; apply: leeD (lexx _) _.
apply: le_trans hbsum _; rewrite lee_fin ler_pdivrMr ?ltr0n // mulr_natr.
by rewrite lerDl; exact: ltW he.
Qed.
