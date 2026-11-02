(** Federer (1969), 3.2.20, p. 257: finite auxiliary
    representatives of total and chart multiplicities for the
    countable integral transformation. The actual counting functions
    are changed only on their proved null exceptional sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalBasic MeasurableRealEmbedding MeasurableExtendedMinimum NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_series_density_representatives]: supporting
    finite-density reduction of the summation in Federer 3.2.20,
    p. 257. The total multiplicity is already proved finite
    almost everywhere by 2.10.11, p. 176. The finite representatives
    preserve every summand almost everywhere, are measurable, and
    obey pointwise domination even on the exceptional set. No new
    global choice operation is exposed. *)
Theorem finite_series_density_representatives (R : realType) (Y : choiceType)
    (nu : set Y -> \bar R) (hn : is_measure nu)
    (N : Y -> \bar R) (Ni : nat -> Y -> \bar R) :
  (forall y,0<=N y) -> (forall i y,0<=Ni i y<=N y) ->
  is_measure_measurable_function nu (partial_function_total (fun y=>(N y:extended_real_line R))) ->
  (forall i,is_measure_measurable_function nu
    (partial_function_total (fun y=>(Ni i y:extended_real_line R)))) ->
  measure_almost_everywhere nu [set y|N y< +oo] ->
  measure_almost_everywhere nu [set y|nonnegative_sum setT (fun i=>Ni i y)=N y] ->
  exists (q : Y -> R) (qi : nat -> Y -> R),
    (forall y,(0<=q y)%R) /\ (forall i y,(0<=qi i y<=q y)%R) /\
    is_measure_measurable_function nu (partial_function_total (fun y=>(q y)%:E : extended_real_line R)) /\
    (forall i,is_measure_measurable_function nu
      (partial_function_total (fun y=>(qi i y)%:E : extended_real_line R))) /\
    measure_almost_everywhere nu [set y|(q y)%:E=N y] /\
    (forall i,measure_almost_everywhere nu [set y|(qi i y)%:E=Ni i y]) /\
    measure_almost_everywhere nu [set y|nonnegative_sum setT (fun i=>(qi i y)%:E)=(q y)%:E].
Proof.
move=> hN0 hNi hNMeas hNiMeas hFinite hSum.
pose q y := fine (N y).
pose qi i y := Num.min (fine (Ni i y)) (q y).
have hFine0 (z : \bar R) : 0<=z -> (0<=fine z)%R.
  by case: z=> [r| |] //=; rewrite lee_fin.
have hq0 y : (0<=q y)%R := hFine0 (N y) (hN0 y).
have hqi i y : (0<=qi i y<=q y)%R.
  apply/andP; split.
  - rewrite /qi le_min (hFine0 (Ni i y) (andP (hNi i y)).1) (hq0 y); reflexivity.
  - by rewrite /qi ge_min lexx orbT.
have hFineMeas (V : Y -> \bar R) :
    is_measure_measurable_function nu (partial_function_total (fun y=>(V y:extended_real_line R))) ->
    is_measure_measurable_function nu (partial_function_total (fun y=>(fine (V y))%:E : extended_real_line R)).
  move=> hV.
  have hh := @measurable_total_borel_postcomposition R Y (extended_real_line R)
    [the topologicalType of real_line_metric R] nu hn
    (fun y=>(V y:extended_real_line R)) (fun z=>(fine z:real_line_metric R))
    hV (@extended_finite_projection_borel R).
  exact: (measurable_total_real_embedding hn hh).
have hqMeas := hFineMeas N hNMeas.
have hqiMeas i : is_measure_measurable_function nu
    (partial_function_total (fun y=>(qi i y)%:E : extended_real_line R)).
  have hh := measurable_total_extended_minimum hn (hFineMeas (Ni i) (hNiMeas i)) hqMeas.
  have he : (fun y=>Order.min (fine (Ni i y))%:E (q y)%:E : extended_real_line R)=
      (fun y=>(qi i y)%:E : extended_real_line R).
    by apply: funext=> y; rewrite /qi EFin_min.
  by rewrite he in hh.
have hValues y : N y< +oo -> (q y)%:E=N y /\ forall i,(qi i y)%:E=Ni i y.
  move=> hFin.
  have hNReal : N y \is a fin_num by rewrite (ge0_fin_numE (hN0 y)).
  have hNVal : (q y)%:E=N y := fineK hNReal.
  split; first exact hNVal.
  move=> i.
  have hNiFin : Ni i y< +oo := le_lt_trans (andP (hNi i y)).2 hFin.
  have hNiReal : Ni i y \is a fin_num by rewrite (ge0_fin_numE (andP (hNi i y)).1).
  have hNiVal : (fine (Ni i y))%:E=Ni i y := fineK hNiReal.
  have hBound : (fine (Ni i y)<=q y)%R.
    rewrite -lee_fin hNiVal hNVal; exact: (andP (hNi i y)).2.
  by rewrite /qi (min_idPl hBound) hNiVal.
exists q,qi; split; first exact hq0.
split; first exact hqi.
split; first exact hqMeas.
split; first exact hqiMeas.
split.
- apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hFinite)=> y hy.
  exact: (hValues y hy).1.
- split.
  + move=> i; apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hFinite)=> y hy.
    exact: (hValues y hy).2 i.
  + apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _
      (measure_almost_everywhere_and hn hFinite hSum))=> y [hy hsy].
    change (nonnegative_sum setT (fun i=>(qi i y)%:E)=(q y)%:E).
    rewrite (hValues y hy).1 -hsy.
    apply: nonnegative_sum_ext=> i _; exact: (hValues y hy).2 i.
Qed.
