(** Federer (1969), 2.5.14, p. 108, proof that every open V is Phi
    measurable. We use half of the requested error for each approximation,
    and retain arbitrary test sets T of finite measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactOpenContentUP CompactOpenContentBasic
  CompactOpenContentSplitting OpenCoverContentUP OpenCoverContentLaws OpenCoverEnvelopeApproximation
  MonotoneDaniellIntegralUP MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_open_envelope_open_measurable]: the open-set
    measurability conclusion in Federer 2.5.14, p. 108 The two abstract cost
    specifications are enough; the proof never computes through their sealed
    constructions. *)
Theorem compact_open_envelope_open_measurable (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a nu : set X -> \bar R)
    (hA : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (ha : is_compact_open_content A a) (hn : is_open_cover_envelope a nu)
    (hm : is_measure nu) V : open V -> measure_measurable nu V.
Proof.
move=> hV; apply: (measure_measurable_finite_test hm V).2=> T hT.
have hTf : nu T \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X nu hm T).
apply/lee_addgt0Pr=> e he.
pose d := (e/2)%R.
have hd : (0 < d)%R by rewrite /d divr_gt0 // ltr0n.
have htd : nu T < nu T+d%:E by rewrite -(fineK hTf) -EFinD lte_fin ltrDl.
have [W [hW [hTW hWa]]] := @open_cover_envelope_strict_approximation R X a nu hn T _ htd.
pose U := W `&` V.
have hU : open U := openI hW hV.
have hUW : U `<=` W by move=> x [hx _].
have haUW := @compact_open_content_mono R X A a ha U W hU hW hUW.
have haf : a U \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@compact_open_content_nonnegative R X A a hA ha U hU).
  apply: le_lt_trans haUW _; apply: lt_trans hWa _.
  rewrite -(fineK hTf) -EFinD; exact: ltry.
have hlow : (fine (a U)-d)%R%:E < a U by rewrite -(fineK haf) lte_fin ltrBlDl ltrDr.
have [f [hf hAf]] := @compact_open_content_strict_approximation R X A a ha U _ hU hlow.
have hcut : a U <= (A f)%:E+d%:E.
  rewrite -(fineK haf) -EFinD lee_fin; apply: ltW.
  by move: hAf; rewrite lte_fin ltrBlDr addrC.
have hfW : is_compact_open_test_function W f.
  split; first exact hf.1.
  split; first exact hf.2.1.
  move=> x hx; exact: (hf.2.2 x hx).1.
have hsplit := @compact_open_content_disjoint_test_bound R X A a hA ha W f hW hfW.
pose Z := W `\` real_function_support f.
have hZ : open Z.
  apply: openI=> //; rewrite openC; exact: real_function_support_closed.
have hTV : T `&` V `<=` U by move=> x [hx hy]; split=> //; exact: hTW x hx.
have hTZ : T `\` V `<=` Z.
  move=> x [hx hnV]; split; first exact: hTW x hx.
  move=> hs; exact: hnV (hf.2.2 x hs).2.
have hb1 := @open_cover_envelope_lower R X a nu hn _ U hU hTV.
have hb2 := @open_cover_envelope_lower R X a nu hn _ Z hZ hTZ.
apply: le_trans (leeD hb1 hb2) _.
apply: le_trans (leeD hcut (lexx (a Z))) _.
have heq : ((A f)%:E+d%:E)+a Z=(a Z+(A f)%:E)+d%:E.
  by rewrite addeAC [(A f)%:E+a Z]addeC.
rewrite heq.
have hbound := leeD hsplit (lexx d%:E).
apply: le_trans hbound _.
have hbound' := leeD (ltW hWa) (lexx d%:E).
apply: le_trans hbound' _.
have hdd : (d+d)%R=e by rewrite -mulr2n -mulr_natr /d divfK // pnatr_eq0.
by rewrite -addeA -EFinD hdd.
Qed.
