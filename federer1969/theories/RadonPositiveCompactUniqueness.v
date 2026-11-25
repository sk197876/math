(** Federer (1969), 4.1.7, p. 358:
    identify the positive density measure from
    its original compact scalar integrals. This
    supporting uniqueness consequence uses the
    compact-test open content of 2.5.14,
    p. 107, and the Radon outer law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RadonMeasureUP FunctionLatticeUP
  CompactSupportFunctionUP RealIntegralFunctionalUP CompactOpenContentUP
  RadonPositiveCompactOpenContent ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_positive_compact_integral_unique]:
    Radon measures representing the same original
    positive compact scalar integral agree on
    every set, supporting Federer 4.1.7, p. 358,
    by 2.5.14, p. 107, and 2.2.5,
    pp. 62–63. Infinite outer masses are retained. *)
Theorem radon_positive_compact_integral_unique (R:realType) (X:topologicalType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (hn:is_measure nu)
    (hr:is_radon_measure mu) (hs:is_radon_measure nu) (F:(X->R)->R):
  is_real_integral_functional mu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_real_integral_functional nu (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  forall A,mu A=nu A.
Proof.
move=>hF hG.
have hMu:=@radon_positive_compact_open_content R X mu hm hr F (radon_locally_compact hr) hF.
have hNu:=@radon_positive_compact_open_content R X nu hn hs F (radon_locally_compact hs) hG.
have hOpen V (hV:open V):mu V=nu V.
  exact:extended_real_supremum_unique (hMu V hV) (hNu V hV).
move=>A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(@radon_outer_greatest R X nu hs A (mu A))=>V hV hAV.
  have hMono:(mu A<=mu V)%E:=@measure_mono R X mu hm A V hAV.
  rewrite (@hOpen V hV) in hMono.
  exact hMono.
- apply:(@radon_outer_greatest R X mu hr A (nu A))=>V hV hAV.
  have hMono:(nu A<=nu V)%E:=@measure_mono R X nu hn A V hAV.
  rewrite -(@hOpen V hV) in hMono.
  exact hMono.
Qed.
