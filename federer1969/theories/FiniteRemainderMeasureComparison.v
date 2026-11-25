(** Finite-tail covering comparison supporting Federer (1969), 2.10.18(1),
    p. 180. A disjoint measurable selection has finite total mu-mass in V;
    retain finitely many members and cover the remainder by their
    enlargements. This lemma isolates its measure calculation from the
    geometric selection theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover MeasureDisjointSupport
  CountablyClosedFamilyUP CoveringFamilyUP NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction NonnegativeFamilyTails NonnegativeSumScale
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_remainder_measure_comparison]: supporting
    selection-tail estimate in 2.10.18(1), p. 180 If selected S cost at most
    a mu(S) and enlarged S cost at most b mu(S), the enlarged tail tends to
    zero, leaving the sharp bound nu(B)<=a mu(V). *)
Theorem finite_remainder_measure_comparison (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (B V : set X) (G : set (set X))
    (E : set X -> set X) (a b : R) :
  is_measure mu -> is_measure nu -> mu V < +oo ->
  set_family_disjoint G -> (forall S, G S -> measure_measurable mu S) ->
  (forall S, G S -> S `<=` V) -> (forall S, G S -> 0<mu S) ->
  (0<=a)%R -> (0<=b)%R ->
  (forall H, finite_set H -> H `<=` G ->
    (B `\` \bigcup_(S in H) S) `<=` \bigcup_(S in G `\` H) E S) ->
  (forall S, G S -> nu S<=a%:E*mu S) ->
  (forall S, G S -> nu (E S)<=b%:E*mu S) -> nu B<=a%:E*mu V.
Proof.
move=> hm hn hV hdis hmeas hwithin hpos ha hb hrem hhead htail.
have hsum := @measure_disjoint_sum_bound R X [the choiceType of set X] mu hm V G idfun hwithin hmeas hdis.
have hsumfin : nonnegative_sum G mu < +oo := le_lt_trans hsum hV.
have hcount : countable G.
  have hc := @measure_disjoint_positive_countable R X [the choiceType of set X] mu hm V G idfun hV hwithin hmeas hdis.
  have he : G `&` [set S | 0<mu S]=G by apply/seteqP; split=> [S [hS _]//|S hS]; split=> //; exact: hpos.
  by rewrite he in hc.
have hvfin : mu V \is a fin_num by rewrite (@ge0_fin_numE R (mu V) (@measure_nonnegative R X mu hm V)).
pose m := fine (mu V).
have hmV : mu V=m%:E by rewrite /m fineK.
rewrite hmV -EFinM.
apply: (@extended_upper_bound_from_scaled_errors R (nu B) (a * m)%R b hb)=> e he.
have [H [hHG [hH hsmall]]] := @nonnegative_family_small_tail R [the choiceType of set X] G mu e
  (fun S _ => @measure_nonnegative R X mu hm S) hsumfin he.
pose T S := if S \in H then S else E S.
have hcover : B `<=` \bigcup_(S in G) T S.
  move=> x hx; case: (pselect ((\bigcup_(S in H) S) x))=> [[S hS hxS]|hnot].
  - exists S; first exact: hHG.
    by rewrite /T (mem_set hS).
  - have [S [hS hSH] hxS] := hrem H hH hHG x (conj hx hnot).
    exists S=> //; rewrite /T.
    have hneq : S \notin H by apply/negP=> /set_mem h; exact: hSH.
    by rewrite (negPf hneq).
have hcov := @measure_indexed_cover R X [the choiceType of set X] nu hn B G T hcount hcover.
have heGH : G `&` H=H by apply/seteqP; split=> [S [_ hS]//|S hS]; split=> //; exact: hHG.
have hsplit := @nonnegative_sum_split R [the choiceType of set X] G H (fun S => nu (T S))
  (fun S _ => @measure_nonnegative R X nu hn (T S)).
rewrite heGH in hsplit.
have hHsum : nonnegative_sum H (fun S => nu (T S))=nonnegative_sum H nu.
  apply: nonnegative_sum_ext=> S hS; by rewrite /T (mem_set hS).
have hTsum : nonnegative_sum (G `\` H) (fun S => nu (T S))=nonnegative_sum (G `\` H) (fun S => nu (E S)).
  apply: nonnegative_sum_ext=> S [hS hnot]; rewrite /T.
  have hneq : S \notin H by apply/negP=> /set_mem h; exact: hnot.
  by rewrite (negPf hneq).
rewrite hHsum hTsum in hsplit; rewrite hsplit in hcov.
have hHbound : nonnegative_sum H nu<=a%:E*mu V.
  have h1 := @nonnegative_sum_mono R [the choiceType of set X] H nu (fun S => a%:E*mu S)
    (fun S hS => hhead S (hHG S hS)).
  rewrite (@nonnegative_sum_scale R [the choiceType of set X] H mu a ha
    (fun S _ => @measure_nonnegative R X mu hm S)) in h1.
  apply: le_trans h1 _; apply: lee_wpmul2l; first by rewrite lee_fin.
  exact: le_trans (@nonnegative_sum_subset R [the choiceType of set X] H G mu hHG) hsum.
have hTbound : nonnegative_sum (G `\` H) (fun S => nu (E S))<=b%:E*e%:E.
  have h1 := @nonnegative_sum_mono R [the choiceType of set X] (G `\` H)
    (fun S => nu (E S)) (fun S => b%:E*mu S) (fun S hS => htail S hS.1).
  rewrite (@nonnegative_sum_scale R [the choiceType of set X] (G `\` H) mu b hb
    (fun S _ => @measure_nonnegative R X mu hm S)) in h1.
  apply: le_trans h1 _; apply: lee_wpmul2l; first by rewrite lee_fin.
  exact: ltW hsmall.
have hfinal := le_trans hcov (leeD hHbound hTbound).
by rewrite hmV -!EFinM -EFinD in hfinal.
Qed.
