(** Federer (1969), 3.2.12, p. 250: apply
    the characteristic expansion of 2.3.3 on almost every
    actual fibre, then 2.4.8. All exceptional measurable
    fibre sets are collected into one conull region. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  CharacteristicFunctionUP CharacteristicFunctionSealed WeightedCharacteristicExpansionUP
  WeightedCharacteristicIntegral MappingMultiplicity NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_characteristic_expansion_inner_integral]:
    the characteristic approximation on fibres in Federer
    3.2.12, p. 250. Every claimed fibre
    integral exists on a proved common conull parameter set;
    its value is the nonnegative sum of characteristic masses. *)
Theorem coarea_characteristic_expansion_inner_integral (R:realType) (X Y:choiceType)
    (p:X->Y) (mu beta:set X->\bar R) (alpha:set Y->\bar R)
    (hb:is_measure beta) (ha:is_measure alpha)
    (u:X->extended_real_line R) (r:nat->R) (E:nat->set X) (s:nat->X->R):
  (forall n,(0<r n)%R) ->is_weighted_characteristic_expansion mu u r E s ->
  (forall n,measure_almost_everywhere alpha
    [set y|measure_measurable beta (mapping_fibre p (E n) y)]) ->
  measure_almost_everywhere alpha [set y|is_measure_integral beta
    (partial_function_zero_extension (0:extended_real_line R) [set x|p x=y] (partial_function_total u))
    (nonnegative_sum setT (fun n=>(r n)%:E*beta (mapping_fibre p (E n) y)))].
Proof.
move=>hr hExp hFibre.
have hAll:=@measure_almost_everywhere_countable R Y [the choiceType of (nat:Type)] alpha ha setT
  (fun n=>[set y|measure_measurable beta (mapping_fibre p (E n) y)])
  (countableP setT) (fun n _=>hFibre n).
apply:(@measure_almost_everywhere_mono R Y alpha ha _ _ _ hAll)=>y hy.
pose B n:=mapping_fibre p (E n) y.
pose t n:=@CharacteristicFunction.value R X (B n).
have ht n:=@CharacteristicFunction.laws R X (B n).
pose v x:extended_real_line R:=if p x==y then u x else 0.
have hRep:is_weighted_characteristic_expansion beta v r B t.
  constructor.
  - move=>n; exact (hy n Logic.I).
  - exact ht.
  - move=>x; case:(pselect (p x=y))=>hx.
    + rewrite /v hx eqxx -(expansion_pointwise_sum hExp x).
      apply:nonnegative_sum_ext=>n _.
      have hValue:t n x=s n x.
        case:(pselect (E n x))=>hE.
        * rewrite (characteristic_on_set (expansion_characteristic_laws hExp n) hE).
          exact (characteristic_on_set (ht n) (conj hE hx)).
        * rewrite (characteristic_off_set (expansion_characteristic_laws hExp n) hE).
          have hnB:~B n x by move=>[hEx _]; exact:hE hEx.
          exact (@characteristic_off_set R X (B n) (t n) (ht n) x hnB).
      by rewrite hValue.
    + rewrite /v (negPf (introN eqP hx)).
      apply:nonnegative_sum_zero=>n _.
      have hOff:t n x= 0%R.
        have hnB:~B n x by move=>[_ h]; exact:hx h.
        exact (@characteristic_off_set R X (B n) (t n) (ht n) x hnB).
      by rewrite hOff mulr0.
have hI:=weighted_characteristic_expansion_integral hb hr hRep.
apply:(measure_integral_graph_equivalent _ hI)=>x z.
case:(pselect (p x=y))=>hx.
- change (v x=z <->partial_function_graph
    (partial_function_zero_extension (0:extended_real_line R) [set x|p x=y] (partial_function_total u)) x z).
  rewrite (@partial_function_zero_extension_on _ _ 0 _ _ x z hx) /v hx eqxx.
  by [].
- change (v x=z <->partial_function_graph
    (partial_function_zero_extension (0:extended_real_line R) [set x|p x=y] (partial_function_total u)) x z).
  rewrite (@partial_function_zero_extension_off _ _ 0 _ _ x z hx) /v (negPf (introN eqP hx)).
  by split=>h; symmetry.
Qed.
