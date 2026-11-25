(** Federer (1969), 3.2.22, pp. 258–259:
    the countable chart-pair cover and disjointness.
    Retain the additional source remainder R required
    by erratum p. 5, book p. 258 lines 20/22. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RectifiableCompactChartsUP RectifiableChartPairPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_remainder_cover]:
    the decomposition of W in Federer 3.2.22,
    p. 258, corrected by erratum p. 5,
    book p. 258 lines 20/22. Add the source
    remainder R=W minus the source-chart union, as
    well as the inverse image of the target remainder Q.
    Neither remainder is silently treated as empty. *)
Theorem rectifiable_chart_pair_remainder_cover (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (psi:nat->R_n R m->R_n R n)
    (C:nat->set (R_n R mu)) (gamma:nat->R_n R mu->R_n R v)
    (F:R_n R n->R_n R v):
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  (forall w,W w ->Z (F w)) ->
  let SrcR:=W `\` (\bigcup_i psi i @` K i) in
  let TarQ:=Z `\` (\bigcup_j gamma j @` C j) in
  W=((W `&` (F @^-1` TarQ)) `|`
      (\bigcup_(p in @setT (nat*nat))
        rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2))) `|` SrcR.
Proof.
move=>hSource hTarget hRange SrcR TarQ; apply/seteqP; split=>w.
- move=>hw; have [hS|hS]:=pselect ((\bigcup_i psi i @` K i) w).
  + have [hT|hT]:=pselect ((\bigcup_j gamma j @` C j) (F w)).
    * have [i _ hSi]:=hS; have [j _ hTj]:=hT.
      left; right; exists (i,j); first exact:Logic.I; by split.
    * left; left; split; first exact hw; split; first exact:(hRange w hw); exact hT.
  + right; by split.
- move=>[[[hw _]|[p _ hPiece]]|[hw _]]; try exact hw.
  exact:((hSource.1 p.1).2 w hPiece.1).
Qed.

(** Source for [rectifiable_chart_pair_pieces_disjoint]:
    the double sum over P_ij in Federer 3.2.22,
    pp. 259–260, is a sum over pairwise disjoint
    sets. Distinct source indices use source-chart
    disjointness; distinct target indices use target-chart
    disjointness after applying F. *)
Theorem rectifiable_chart_pair_pieces_disjoint (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v))
    (K:nat->set (R_n R m)) (psi:nat->R_n R m->R_n R n)
    (C:nat->set (R_n R mu)) (gamma:nat->R_n R mu->R_n R v)
    (F:R_n R n->R_n R v):
  is_rectifiable_compact_chart_cover lambda W K psi ->
  is_rectifiable_compact_chart_cover lambda Z C gamma ->
  forall p q:nat*nat,p<>q ->
    rectifiable_chart_pair_piece (K p.1) (C p.2) (psi p.1) F (gamma p.2) `&`
    rectifiable_chart_pair_piece (K q.1) (C q.2) (psi q.1) F (gamma q.2)=set0.
Proof.
move=>hSource hTarget [i j] [s t] hDifferent; apply/seteqP; split=>[w [[hSi hTj] [hSs hTt]]|w []].
have [his|his]:=eqVneq i s.
- have [hjt|hjt]:=eqVneq j t.
  + apply:hDifferent; by rewrite his hjt.
  + exact:(hTarget.2.1 j t hjt (F w) hTj hTt).
- exact:(hSource.2.1 i s his w hSi hSs).
Qed.
