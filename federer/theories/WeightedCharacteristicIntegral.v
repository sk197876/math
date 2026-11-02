(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  CharacteristicFunctionUP WeightedCharacteristicExpansionUP NonnegativeSum MeasureIntegralUP
  MeasureFiniteCharacteristicIntegral DensityCharacteristicIntegral MeasureIntegralGraphEquivalence TotalNonnegativeSeriesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_characteristic_expansion_integral]: the
    nonnegative-series step in Federer 2.4.18(1), proof p. 91, using 2.3.3
    and 2.4.8 Any positive weight expansion is permitted, as in Federer,
    rather than fixing harmonic weights. *)
Lemma weighted_characteristic_expansion_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> extended_real_line R)
    (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  (forall n, (0 < r n)%R) -> is_weighted_characteristic_expansion mu f r A g ->
  is_measure_integral mu (partial_function_total f)
    (nonnegative_sum setT (fun n => (r n)%:E * mu (A n))).
Proof.
move=> hr he.
have hg n x : (0 <= g n x)%R.
  have [hx|hx] := pselect (A n x).
  - by rewrite (characteristic_on_set (expansion_characteristic_laws he n) hx).
  - by rewrite (characteristic_off_set (expansion_characteristic_laws he n) hx).
have hi n : is_measure_integral mu
    (partial_function_total (fun x => ((r n * g n x)%R%:E : extended_real_line R)))
    ((r n)%:E * mu (A n)).
  have h := @measure_positive_characteristic_integral R X mu hm (A n) (g n) (r n)
    (expansion_characteristic_laws he n) (expansion_sets_measurable he n) (hr n).
  exact: measure_integral_graph_equivalent (real_total_embedding_graph _) h.
have hnon n x : 0 <= (r n * g n x)%R%:E.
  rewrite lee_fin; exact: mulr_ge0 (ltW (hr n)) (hg n x).
have hs := @total_nonnegative_series_integral R X mu hm
    (fun n x => ((r n * g n x)%R%:E : extended_real_line R)) _ hnon hi.
have hfun : (fun x => nonnegative_sum setT (fun n => (r n * g n x)%R%:E))=f.
  apply/funext=> x; exact: (expansion_pointwise_sum he x).
by rewrite hfun in hs.
Qed.
