(** Federer (1969), 3.2.31, pp. 268–269: supporting
    Borel measurability of the compact source's fibre-threshold
    sets, from 2.10.26, pp. 189–190. Rational order density
    changes the known closed sublevels into closed superlevels. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology HausdorffFibreCutoffs
  CompactFibreMeasurability TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_fibre_mass_closed_superlevel_borel]:
    supporting the assertion that Z is Borel in the compact
    case of Federer 3.2.31, p. 269, using 2.10.26, p. 190.
    The inequality is the printed non-strict threshold. Infinite
    fibre masses and all real thresholds are retained. *)
Theorem compact_fibre_mass_closed_superlevel_borel (R:realType) (X Y:metricType R)
    (f:X->Y) (K:set X) k (t:R):
  continuous f ->compact K ->
  borel_set [set y|t%:E<=hausdorff_fibre_mass f K k y].
Proof.
move=>hf hK.
pose D:=[set q:rat|((ratr q:R)<t)%R].
pose A q:=[set y:Y|(ratr q:R)%:E<hausdorff_fibre_mass f K k y].
have hA q:borel_set (A q).
  have hEq:A q=~` [set y:Y|hausdorff_fibre_mass f K k y<=(ratr q:R)%:E].
    apply/seteqP; split=>y /=.
    - move=>hy hLe; have hFalse:=le_lt_trans hLe hy; by rewrite ltxx in hFalse.
    - move=>hNot; change (is_true ((ratr q:R)%:E<hausdorff_fibre_mass f K k y)).
      rewrite ltNge; exact/negP.
  rewrite hEq; apply:borel_set_complement.
  exact:compact_fibre_mass_closed_level_borel hf hK.
have hEq:[set y:Y|t%:E<=hausdorff_fibre_mass f K k y]=\bigcap_(q in D) A q.
  apply/seteqP; split=>y.
  - move=>hy q hq; apply:lt_le_trans _ hy; rewrite lte_fin; exact hq.
  - move=>hy; change (is_true (t%:E<=hausdorff_fibre_mass f K k y)).
    rewrite leNgt; apply/negP=>hBad.
    have [q [hLower hUpper]]:=@extended_rationals_order_dense R _ _ hBad.
    have hq:D q by move:hUpper; rewrite lte_fin.
    have hFalse:=lt_trans hLower (hy q hq); by rewrite ltxx in hFalse.
rewrite hEq; apply:(@borel_set_countable_intersection Y [the choiceType of (rat:Type)] D A (countableP _) _).
- have [q [_ hqt]]:=@extended_rationals_order_dense R -oo t%:E (ltNyr t).
  exists q; move:hqt; by rewrite lte_fin.
- move=>q hq; exact:hA.
Qed.
