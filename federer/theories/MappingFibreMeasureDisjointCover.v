(** Federer (1969), 3.2.22, pp. 259–260:
    countable additivity of the Hausdorff fibre masses
    with a null omitted fibre. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal.
From Federer Require Import NonnegativeSum MappingMultiplicity MappingFibreSetAlgebra
  MeasureUP MeasureBasic MeasureSplit MeasureCountableAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_fibre_measure_disjoint_cover]:
    the fibre sum in Federer 3.2.22, p. 259,
    by 2.1.3(3), p. 55. Countably many
    disjoint measurable subfibres account for the entire
    fibre measure when its omitted remainder is null.
    The original fibre may have infinite measure and
    is not assumed measurable in this supporting lemma. *)
Theorem mapping_fibre_measure_disjoint_cover (R:realType) (X I:choiceType) (Y:Type)
    (rho:set X->\bar R) (hr:is_measure rho) (F:X->Y) (A:set X)
    (D:set I) (P:I->set X) z:
  countable D ->(forall i,D i ->P i `<=` A) ->
  (forall i j,D i ->D j ->i<>j ->P i `&` P j=set0) ->
  (forall i,D i ->measure_measurable rho (mapping_fibre F (P i) z)) ->
  rho (mapping_fibre F (A `\` (\bigcup_(i in D) P i)) z)=0 ->
  rho (mapping_fibre F A z)=nonnegative_sum D (fun i=>rho (mapping_fibre F (P i) z)).
Proof.
move=>hCount hSub hDisjoint hMeas hNull.
pose U:=\bigcup_(i in D) mapping_fibre F (P i) z.
pose E:=mapping_fibre F A z.
have hUE:U `<=` E by move=>x [i hi [hPi hValue]]; split; [exact:(hSub i hi x hPi)|exact hValue].
have hRemainder:rho (E `\` U)=0 by rewrite -mapping_fibre_chart_remainder.
have hCover:E `<=` U `|` (E `\` U).
  move=>x hx; have [hU|hU]:=pselect (U x); [by left|right; by split].
have hUpper:=measure_binary_cover hr hCover.
rewrite hRemainder adde0 in hUpper.
have hValue:rho E=rho U by apply/eqP; rewrite eq_le hUpper (measure_mono hr hUE).
rewrite hValue.
apply:(measure_countable_disjoint_additivity hr hCount hMeas)=>i j hi hj hNe x [hPi _] [hPj _].
have hDifferent:i<>j by move=>hEq; by rewrite hEq eqxx in hNe.
have hEmpty:=hDisjoint i j hi hj hDifferent; have hMember:(P i `&` P j) x:=conj hPi hPj.
by rewrite hEmpty in hMember.
Qed.
