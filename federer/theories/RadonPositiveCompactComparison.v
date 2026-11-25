(** Federer (1969), 4.1.7, p. 359:
    positive compact scalar integral comparison
    gives comparison of every original outer
    measure. This supporting consequence reuses
    the compact-test content of 2.5.14,
    p. 107, and Radon outer regularity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RadonMeasureUP FunctionLatticeUP CompactSupportFunctionUP
  RealIntegralFunctionalUP CompactOpenContentUP RadonPositiveCompactOpenContent ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_positive_compact_integral_comparison]:
    order of the original positive compact
    integrals implies order on every set,
    supporting the sharp weighted variation in
    Federer 4.1.7, p. 359. Arbitrary
    infinite outer masses remain permitted. *)
Theorem radon_positive_compact_integral_comparison (R:realType) (X:topologicalType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (hn:is_measure nu)
    (hr:is_radon_measure mu) (hs:is_radon_measure nu) (F G:(X->R)->R):
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F->
  is_real_integral_functional nu (positive_function_lattice (@compactly_supported_continuous_functions R X)) G->
  (forall f,positive_function_lattice (@compactly_supported_continuous_functions R X) f->(F f<=G f)%R)->
  forall A,mu A<=nu A.
Proof.
move=>hF hG hOrder.
have hMu:=@radon_positive_compact_open_content R X mu hm hr F (radon_locally_compact hr) hF.
have hNu:=@radon_positive_compact_open_content R X nu hn hs G (radon_locally_compact hs) hG.
have hOpen O (hO:open O):mu O<=nu O.
  apply:(extended_real_supremum_least (hMu O hO))=>c [f [hTest ->]].
  have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) f.
    split;first exact:hTest.1.
    move=>x;exact:(andP (hTest.2.1 x)).1.
  have hUpper:(G f)%:E<=nu O.
    apply:(extended_real_supremum_upper (hNu O hO)).
    exists f;by split.
  apply:(le_trans _ hUpper).
  rewrite lee_fin;exact:hOrder f hPositive.
move=>A;apply:(@radon_outer_greatest R X nu hs A (mu A))=>O hO hAO.
exact:(le_trans (measure_mono hm hAO) (hOpen O hO)).
Qed.
