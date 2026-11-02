(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FiniteCompactMassUP MeasureUP MeasureBasic MeasureSplit ExtendedRealBounds ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_compact_mass_sequence_exists]: supporting
    construction of Federer's increasing supremum-approaching
    sequence, 2.10.48, p. 206. Reciprocal-error choices followed
    by finite unions prove existence of the abstract laws. *)
Theorem finite_compact_mass_sequence_exists (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) (M : R) :
  is_measure mu ->
  (forall C, compact C -> C `<=` S -> mu C< +oo -> mu C<=M%:E) ->
  exists F, is_finite_compact_mass_sequence mu S F.
Proof.
move=> hm hb.
pose V := finite_compact_mass_values mu S.
pose s := extended_real_sup V.
have h0 : V 0.
  exists set0; split; [exact: compact0|by move=> x []|by rewrite (measure_empty hm) ltry|exact: esym (measure_empty hm)].
have hs0 : 0<=s := extended_real_sup_upper h0.
have hsM : s<=M%:E.
  apply: extended_real_sup_least=> b [C [hC hCS hfin ->]]; exact: hb.
have hsfin : s \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr (0%R : R)) hs0.
  - exact: le_lt_trans hsM (ltry M).
pose a := fine s.
have hsa : s=a%:E by rewrite /a fineK.
have happ (e : R) : (0<e)%R -> exists C,
    [/\ compact C, C `<=` S, mu C< +oo & (a-e)%:E<mu C].
  move=> he; apply: contrapT=> hnone.
  have hle : s<=(a-e)%:E.
    apply: extended_real_sup_least=> b [C [hC hCS hfin ->]].
    rewrite leNgt; apply/negP=> hlt; apply: hnone; by exists C.
  have hlt : (a-e)%:E<s by rewrite hsa lte_fin ltrBlDr ltrDl.
  by move: hlt; rewrite ltNge hle.
have hap n : exists C, [/\ compact C, C `<=` S, mu C< +oo & (a-(n.+1%:R)^-1)%:E<mu C].
  apply: happ; by rewrite invr_gt0 ltr0n.
pose u n := projT1 (cid (hap n)).
have hu n := projT2 (cid (hap n)).
pose F := fix F (n : nat) : set X :=
  match n with 0%N => u 0%N | k.+1 => F k `|` u k.+1 end.
have hF n : [/\ compact (F n), F n `<=` S & mu (F n)< +oo].
  elim: n=> [|n [hC hCS hfin]].
  - have [h1 h2 h3 _] := hu 0%N; by split.
  - have [h1 h2 h3 _] := hu n.+1; split.
    + exact: compactU hC h1.
    + by move=> x [hx|hx]; [exact: hCS|exact: h2].
    + have hcov := @measure_binary_cover R X mu hm (F n `|` u n.+1) (F n) (u n.+1) (fun x hx=>hx).
      have hsum : mu (F n)+mu (u n.+1)< +oo := lte_add_pinfty hfin h3.
      exact (le_lt_trans hcov hsum).
have hmono : forall n m, (n<=m)%N -> F n `<=` F m.
  move=> n m; elim: m=> [|m IH] in n * .
  - by rewrite leqn0=> /eqP -> x hx.
  - rewrite leq_eqVlt; move=> /orP[/eqP ->|hn] x hx; first exact hx.
    left; exact: IH n hn x hx.
have huF n : u n `<=` F n by case: n=> [|n] x hx; [exact hx|right].
pose U := \bigcup_n F n.
have haU : a%:E<=mu U.
  rewrite leNgt; apply/negP=> hUa.
  have hU0 := @measure_nonnegative R X mu hm U.
  have hUfin : mu U \is a fin_num.
    rewrite fin_numElt; apply/andP; split.
    - exact: lt_le_trans (ltNyr (0%R : R)) hU0.
    - exact: lt_trans hUa (ltry a).
  have hUe : mu U=(fine (mu U))%:E by rewrite fineK.
  rewrite hUe lte_fin in hUa.
  have he : (0<a-fine (mu U))%R by rewrite subr_gt0.
  have [n hn] := @positive_reciprocal_nat_small R _ he.
  have [_ _ _ hnear] := hu n.
  have hbound : mu (u n)<=mu U.
    apply: (@measure_mono R X mu hm)=> x hx; exists n=> //; exact: huF hx.
  have hh := lt_le_trans hnear hbound; rewrite hUe lte_fin in hh.
  have hdist : (a-fine (mu U)<(n.+1%:R)^-1)%R.
    by rewrite ltrBlDr addrC -ltrBlDr.
  have hbad := lt_trans hn hdist; by rewrite ltxx in hbad.
exists F; constructor=> // C hC hCS hfin.
apply: le_trans _ haU; rewrite -hsa; apply: extended_real_sup_upper.
exists C; by split.
Qed.
