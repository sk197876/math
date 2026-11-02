(** Federer (1969), 3.2.13, p. 250: supporting
    finite-integrability criterion for Euler Gamma. A countable
    measurable cover with summable constant costs supplies an
    actual integrable majorant by 2.4.8. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral MeasureIntegralComparison
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  TotalCountableNonnegativeIntegral NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_integral_majorant_finite]: the
    summable-cover estimate used to establish the defining
    Gamma integral in Federer 3.2.13, p. 250.
    The cover may overlap, have empty members or contain
    sets of infinite mass with zero cost. No disjointness,
    finite ambient measure or external integration result is assumed. *)
Theorem countable_integral_majorant_finite (R:realType) (X:choiceType) (J:countType)
    (mu:set X->\bar R) (hm:is_measure mu) (u:X->extended_real_line R)
    (B:J->set X) (c:J->R):
  is_measure_measurable_function mu (partial_function_total u) ->(forall x,0<=u x) ->
  (forall n,measure_measurable mu (B n)) ->(forall n,(0<=c n)%R) ->
  (forall n x,B n x ->u x<=(c n)%:E) ->
  (forall x,0<u x ->exists n,B n x) ->
  nonnegative_sum setT (fun n=>(c n)%:E*mu (B n))< +oo ->
  exists a:R,(0<=a)%R /\is_measure_integral mu (partial_function_total u) a%:E.
Proof.
move=>hu hp hB hc hBound hCover hCost.
pose chi n:=@CharacteristicFunction.value R X (B n).
have hChi n:=@CharacteristicFunction.laws R X (B n).
pose v n x:extended_real_line R:=(c n)%:E*(chi n x)%:E.
have hV n x:0<=v n x.
  apply:mule_ge0; first by rewrite lee_fin.
  exact (characteristic_extended_nonnegative (hChi n) x).
have hVI n:is_measure_integral mu (partial_function_total (v n)) ((c n)%:E*mu (B n)).
  have hcE:0<=(c n)%:E by rewrite lee_fin.
  exact (measure_nonnegative_extended_characteristic_integral hm (hChi n) (hB n) hcE).
have hMajor:=@total_countable_nonnegative_integral R X J mu hm setT v
  (fun n=>(c n)%:E*mu (B n)) (countableP _)
  (fun n _=>hV n) (fun n _=>hVI n).
have hPoint x:u x<=nonnegative_sum setT (fun n=>v n x).
  case:(ltP 0 (u x))=>[hx|hx].
  - have [n hn]:=hCover x hx.
    apply:le_trans (hBound n x hn) _.
    have hTerm:=@nonnegative_sum_term R J setT (fun j=>v j x) n Logic.I.
    have hOn:chi n x= 1%R:=characteristic_on_set (hChi n) hn.
    by rewrite /v hOn mule1 in hTerm.
  - have hZero:u x= 0 by apply/eqP; rewrite eq_le hx hp.
    rewrite hZero; exact:nonnegative_sum_nonnegative.
have hPositive:measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total u)).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  exists (u x); by split.
have [hI hNonnegative]:=nonnegative_measurable_function_integral hm hu hPositive.
have hUpper:measure_lower_integral mu (partial_function_total u)<=
    nonnegative_sum setT (fun n=>(c n)%:E*mu (B n)).
  apply:(measure_integral_monotone hm hI hMajor).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  exists (u x),(nonnegative_sum setT (fun n=>v n x)); split; first by [].
  split; first by [].
  exact:hPoint.
have hFinite:measure_lower_integral mu (partial_function_total u) \is a fin_num.
  rewrite ge0_fin_numE //; exact:le_lt_trans hUpper hCost.
exists (fine (measure_lower_integral mu (partial_function_total u))); split.
- by rewrite -lee_fin fineK.
- by rewrite fineK.
Qed.
