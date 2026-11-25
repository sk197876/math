(** Compactness from the line-section laws of Federer (1969), 2.10.30, p.
    195. A compact source has compact projection and upper semicontinuous
    section length. These facts make its centred-section replacement closed,
    and then compact inside the product of the compact projection and a
    bounded scalar interval. The proof uses the abstract section laws, not
    an unfolded symmetrisation construction. it does not separately prove
    this compactness assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground ProductSections TopologicalProductMaps
  CompactProductSections CompactScalarProductSections CompactMaximum
  CenteredSectionUP CenteredSectionLaws CenteredSectionBounds LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_centered_product_closed]: supporting
    closedness of T for the compactness conclusion
    in 2.10.30, p. 195. Empty-section support
    is used at points of the central hyperplane;
    length bounds alone would not suffice there. *)
Theorem compact_centered_product_closed (R : realType) (P : topologicalType)
    (K T : set (P*real_line_metric R)) :
  hausdorff_space P -> compact K ->
  (forall p, is_centered_section (product_vertical_section K p) (product_vertical_section T p)) ->
  closed T.
Proof.
move=> hP hK hs.
pose D := fst @` K.
have hDc : closed D := compact_closed hP (compact_product_first_projection hK).
have hlocal : forall z, ~T z -> exists O, open O /\ O z /\ O `<=` ~` T.
  move=> [p t] hnot; case: (pselect (D p))=> [hp|hp].
  - have hne : product_vertical_section K p !=set0.
      have [[q s] hqs hq] := hp; change (q=p) in hq.
      exists s; by rewrite /product_vertical_section /= -hq.
    have [r [hr [hlen hmem]]] := centered_section_membership (hs p) hne.
    have hrt : r<`|t|.
      rewrite ltNge; apply/negP=> ht; apply: hnot; exact: (hmem t).2 ht.
    pose b := r+`|t|.
    have hb : (lebesgue_scalar_measure (product_vertical_section K p)<b%:E)%E.
      by rewrite hlen lte_fin /b ltrD2l.
    have [V [hV [hpV hVB]]] := @compact_scalar_product_section_upper R P K p b hP hK hb.
    pose W : set (real_line_metric R) := [set s | b<`|s|+`|s|].
    have hW : open W.
      have hf : continuous (fun s : real_line_metric R => (`|s|+`|s| : R^o)).
        move=> s; apply: continuousD; exact (@norm_continuous R R^o s).
      apply: open_comp (@open_gt R b)=> s _; exact: hf.
    exists (V `*` W); split.
    + apply: openI.
      * apply: open_comp hV=> z _; exact: first_projection_continuous.
      * apply: open_comp hW=> z _; exact: second_projection_continuous.
    split; first by split=> //; change (is_true (b<`|t|+`|t|)); rewrite /b ltrD2r.
    move=> [q s] [hq hsW] hqs.
    have hneT : product_vertical_section T q !=set0 by exists s.
    have hneK := (centered_section_support_law (hs q)).2 hneT.
    have [a [ha [hlenq hmq]]] := centered_section_membership (hs q) hneK.
    have hs0 := (hmq s).1 hqs.
    have hqb := hVB q hq; rewrite hlenq lte_fin in hqb.
    change (is_true (b<`|s|+`|s|)) in hsW.
    lra.
  - exists ((~` D) `*` setT); split.
    + apply: openI.
      * apply: open_comp (closed_openC hDc)=> z _; exact: first_projection_continuous.
      * exact: openT.
    split; first by split.
    move=> [q s] [hq _] hqs.
    have hneT : product_vertical_section T q !=set0 by exists s.
    have [v hv] := (centered_section_support_law (hs q)).2 hneT.
    apply: hq; by exists (q,v).
have ho : open (~` T).
  rewrite openE=> z hz; have [O [hO [hzO hsub]]] := hlocal z hz.
  apply: filterS hsub _; apply: open_nbhs_nbhs; by split.
have hh := open_closedC ho; by rewrite setCK in hh.
Qed.

(** Source for [compact_centered_product]: direct compactness
    assertion in 2.10.30, p. 195, in
    scalar product coordinates. The parameter factor can
    be any Hausdorff space. Empty sources are included. *)
Theorem compact_centered_product (R : realType) (P : topologicalType)
    (K T : set (P*real_line_metric R)) :
  hausdorff_space P -> compact K ->
  (forall p, is_centered_section (product_vertical_section K p) (product_vertical_section T p)) ->
  compact T.
Proof.
move=> hP hK hs.
have hc := compact_centered_product_closed hP hK hs.
case: (pselect (K !=set0))=> [hne|hne].
- have hf : continuous (fun z : P*real_line_metric R => (`|z.2| : R^o)).
    move=> z; exact (continuous_comp (@second_projection_continuous P (real_line_metric R) z)
      (@norm_continuous R R^o z.2)).
  have [z [hz hmax]] := continuous_compact_maximum hne hK hf.
  pose r := `|z.2|.
  have hr : 0<=r := normr_ge0 _.
  have hprod : compact ((fst @` K) `*` `[-r,r]).
    exact (compact_setX (compact_product_first_projection hK) (@segment_compact R (-r) r)).
  apply: (subclosed_compact hc hprod)=> -[p t] hpt.
  have hneT : product_vertical_section T p !=set0 by exists t.
  have [s hsK] := (centered_section_support_law (hs p)).2 hneT.
  split; first by exists (p,s).
  rewrite /= in_itv /= -ler_norml.
  exact (@centered_section_norm_bound R (product_vertical_section K p)
    (product_vertical_section T p) r (hs p) hr (fun v hv=>hmax (p,v) hv) t hpt).
- have hzero : T=set0.
    apply/seteqP; split=> -[p t]; last by case.
    move=> hpt; exfalso; apply: hne.
    have hneT : product_vertical_section T p !=set0 by exists t.
    have [s hsK] := (centered_section_support_law (hs p)).2 hneT.
    by exists (p,s).
  rewrite hzero; exact: compact0.
Qed.
