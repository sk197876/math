(** Federer (1969), 3.2.20, p. 257: assemble the
    disjoint compact-chart formulas, including arbitrary extended-real
    weights and exact signed definedness. The independent decomposition
    laws are all proved in the geometric application. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureIntegralUP MeasureIntegralAlmostEquality
  CountableAreaDecompositionUP FiniteSeriesDensityRepresentatives CountableWeightedIntegralTransport
  NonnegativeWeightedTransportParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_area_decomposition_transform]: supporting
    complete summation argument in Federer 3.2.20, p. 257,
    using 2.4.8, p. 84, then 2.4.4(6), p. 82. Finite
    representatives are used only on proved conull sets, and the
    conclusion retains the original multiplicity. Both infinite
    integral values and undefined signed differences are matched. *)
Theorem countable_area_decomposition_transform (R : realType)
    (X Y Z : choiceType) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (pi : nat -> X -> R)
    (N : Y -> \bar R) (Ni : nat -> Y -> \bar R) :
  is_countable_area_decomposition mu nu u v p pi N Ni -> forall (g : Z -> \bar R) a,
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (p x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* N y : extended_real_line R)) a.
Proof.
move=> [hp hpi hpM hpiM hPSum hN0 hNi hNM hNiM hNFin hNSum hLocal].
have [q [qi [hq0 [hqi [hqM [hqiM [hEq [hEqi hQSum]]]]]]]] :=
  finite_series_density_representatives hn hN0 hNi hNM hNiM hNFin hNSum.
have hTarget (g : Z -> \bar R) : measure_almost_equal nu
    (partial_function_total (fun y=>g (v y)* N y : extended_real_line R))
    (partial_function_total (fun y=>g (v y)* (q y)%:E : extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hEq)=> y hy.
  exists (g (v y)* N y); split; first reflexivity.
  by change (g (v y)* (q y)%:E=g (v y)* N y); rewrite hy.
have hPiece (g : Z -> \bar R) i : measure_almost_equal nu
    (partial_function_total (fun y=>g (v y)* Ni i y : extended_real_line R))
    (partial_function_total (fun y=>g (v y)* (qi i y)%:E : extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ (hEqi i))=> y hy.
  exists (g (v y)* Ni i y); split; first reflexivity.
  by change (g (v y)* (qi i y)%:E=g (v y)* Ni i y); rewrite hy.
have hLocalQ (g : Z -> \bar R) i a :
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (pi i x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* (qi i y)%:E : extended_real_line R)) a.
  split=> hI.
  - exact: (measure_integral_almost_equal hn ((hLocal g i a).1 hI) (hPiece g i)).
  - have hOld := measure_integral_almost_equal hn hI (measure_almost_equal_sym (hPiece g i)).
    exact: (hLocal g i a).2 hOld.
have hPi0 i x : 0<=(pi i x)%:E.
  rewrite lee_fin; exact: (andP (hpi i x)).1.
have hQi0 i y : 0<=(qi i y)%:E.
  rewrite lee_fin; exact: (andP (hqi i y)).1.
have hNonnegativeQ (g : Z -> \bar R) (hg : forall z,0<=g z) a :
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (p x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* (q y)%:E : extended_real_line R)) a.
  split.
  - exact: (@countable_weighted_integral_transport_forward R X Y Z mu nu hm hn u v p pi
      (fun y=>(q y)%:E) (fun i y=>(qi i y)%:E) hp hpi hQi0 hpM hpiM hPSum hQSum
      (fun h hh i b=>(hLocalQ h i b).1) g hg a).
  - exact: (@countable_weighted_integral_transport_forward R Y X Z nu mu hn hm v u q qi
      (fun x=>(p x)%:E) (fun i x=>(pi i x)%:E) hq0 hqi hPi0 hqM hqiM hQSum hPSum
      (fun h hh i b=>(hLocalQ h i b).2) g hg a).
have hNonnegative (g : Z -> \bar R) (hg : forall z,0<=g z) a :
    is_measure_integral mu (partial_function_total (fun x=>g (u x)* (p x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>g (v y)* N y : extended_real_line R)) a.
  split=> hI.
  - have hNew := (hNonnegativeQ g hg a).1 hI.
    exact: (measure_integral_almost_equal hn hNew (measure_almost_equal_sym (hTarget g))).
  - have hNew := measure_integral_almost_equal hn hI (hTarget g).
    exact: (hNonnegativeQ g hg a).2 hNew.
have hpE x : 0<=(p x)%:E by rewrite lee_fin.
exact: (@nonnegative_weighted_transport_signed R X Y Z mu nu hm hn u v
  (fun x=>(p x)%:E) N hpE hN0 hNonnegative).
Qed.
