(** Federer (1969), 3.2.38, p. 275: actual scalar integrand
    values with small oscillation give the good-core cell estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureSubsetIntegral FiniteSubsetIntegralOscillationLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_subset_actual_value_lower]: supporting the
    pointwise Jacobian comparison inside the compact Lusin core in
    Federer 3.2.38, p. 275. All values J(x) are actual graph
    values on A; their oscillation from c is bounded by e. The
    subset integral and its precise original domain are retained.
    Only finite source mass is required, not finite integral value. *)
Lemma finite_subset_actual_value_lower (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (u:partial_function X (extended_real_line R))
    (J:X->R) (I : \bar R) (c e:R):
  is_measure mu ->measure_measurable mu A ->(mu A< +oo)%E ->(0<=I)%E ->
  is_measure_subset_integral mu A u I ->
  (forall x,A x ->partial_function_graph u x (J x)%:E /\`|c-J x|<=e) ->
  (c%:E*mu A<=I+e%:E*mu A)%E.
Proof.
move=>hm hA hFinite hI0 hIntegral hValues.
have hMassFinite:mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hMass:mu A=(fine (mu A))%:E by rewrite fineK.
have hLower:measure_almost_everywhere_on mu A
    [set x|exists z,partial_function_graph u x z /\(c-e)%R%:E<=z]%E.
  have hEmpty:(A `\` [set x|exists z,partial_function_graph u x z /\(c-e)%R%:E<=z]%E)=set0.
    apply/seteqP; split=>[x [hx hNot]|x []].
    exfalso; apply:hNot; have [hValue hDistance]:=hValues x hx.
    exists (J x)%:E; split=>//; rewrite lee_fin.
    rewrite ler_norml in hDistance; have /andP[hlo hhi]:=hDistance; lra.
  by rewrite /measure_almost_everywhere_on hEmpty; exact:measure_empty hm.
have hBound:=@finite_subset_integral_oscillation_lower R X mu A u I c e (fine (mu A))
  hm hA hMass hI0 hIntegral hLower.
have hRight:(e%:E*mu A=(e*fine (mu A))%R%:E)%E.
  by rewrite hMass -EFinM.
rewrite hRight; exact hBound.
Qed.
