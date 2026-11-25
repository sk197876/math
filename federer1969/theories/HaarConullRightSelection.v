(** Federer (1969), 3.4.8(13), p. 336:
    one rotation lies in every required right translate
    of the conull reduction set. This follows directly
    from the existing right Haar invariance and countable
    conjunction laws; the selection is a local witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws HaarIntegralUP HaarIntegralLaws
  CompactGroupHaarNormalisation GroupMultiplicationHomogeneous InvariantMeasureTranslates
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostPositiveWitness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [haar_conull_right_selection]: the simultaneous
    choice g psi_lambda in E_m of 3.4.8(13),
    p. 336. A countable family is allowed,
    and no measurability premise on the conull set
    is added. *)
Theorem haar_conull_right_selection (R:realType) (G:topologicalType)
    (mul:G->G->G) (inv:G->G) (one:G)
    (hGc:is_locally_compact_hausdorff_group mul inv one)
    (hCompact:compact [set:G]) (theta:set G->\bar R)
    (J:choiceType) (D:set J) (psi:J->G) (P:set G):
  is_normalised_haar_measure mul theta ->countable D ->
  measure_almost_everywhere theta P ->
  exists g,forall j,D j ->P (mul g (psi j)).
Proof.
move=>hTheta hCount hAlmost.
have hRight:=normalised_haar_measure_right hGc hCompact hTheta.
have hInvariant:=nonzero_invariant_measure_invariant hRight.
have hTopological:=lch_group_topological hGc.
have hGroup:=topological_group_laws hTopological.
have hHomogeneous:=right_multiplication_homogeneous hTopological.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
have hEach j:measure_almost_everywhere theta [set g|P (mul g (psi j))].
  rewrite /measure_almost_everywhere.
  have hPreimage:=@invariant_measure_preimage R G G mul inv one
    (right_multiplication_action mul inv) hGroup hHomogeneous theta hInvariant (inv (psi j)) (~` P).
  rewrite /right_multiplication_action (group_invK hGroup) in hPreimage.
  exact:eq_trans hPreimage hAlmost.
have hAll:=@measure_almost_everywhere_countable R G J theta hMeasure D
  (fun j=>[set g|P (mul g (psi j))]) hCount (fun j _=>hEach j).
have hMass:theta setT<>0%E.
  rewrite hTheta.2;move=>hEqual.
  have hOne:(1:R)=0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have [g [_ hGood]]:=measure_almost_positive_set_witness hMeasure hMass hAll.
by exists g.
Qed.
