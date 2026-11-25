(** Federer (1969), 2.5.9, p. 100: existence of the continuous norm-one
    extension. The positive-cone route respects erratum p. 2, book p. 100
    line 22. Positive and negative parts extend the already proved
    positive-cone functional; its Lipschitz law gives the full norm bound
    directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP RealIntegralFunctionalUP
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm
  FunctionSeminormDistance PositiveLoneFunctionalExtension PositiveDifferenceFunctional
  PositiveDifferenceLinear DominatedLoneExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_lone_extension_exists]: the actual
    extension required by Federer 2.5.9, p. 100.
    Positive density is proved upstream from the regular representing
    measure; no extension or linearity assumption is added. *)
Theorem dominated_lone_extension_exists (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_function_lattice_regular L mu -> is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) ->
  exists S, is_dominated_lone_extension mu L A S.
Proof.
move=> hF hrepr hr hA hb.
have [B [hB [hB0 [hadd hscale]]]] := @positive_lone_functional_extension_exists
  R X L hL F A mu hm hF hrepr hr hA hb.
pose S := positive_difference_functional B.
have hV := @total_scalar_lp_vector_lattice R X mu hm 1 (lexx _).
exists S; split.
- exact: (@positive_difference_functional_linear R X _ hV B hadd hscale).
- split.
  + move=> f hf.
    pose p x := Order.max (f x) 0%R; pose q x := Order.max (-f x)%R 0%R.
    have [hp hq] := @positive_parts_membership R X L hL f hf.
    have headd : (fun x => (f x+q x)%R)=p.
      apply: funext=> x.
      have he : (p x-q x)%R=f x := congr1 (fun u => u x) (positive_parts_difference f).
      by rewrite -he subrK.
    have ha := @daniell_integral_add R X L A hA f q hf hq.1; rewrite headd in ha.
    change (B p-B q=A f)%R.
    by rewrite (hB.1 p hp) (hB.1 q hq) ha addrK.
  + move=> f hf; have [hp hq] := @positive_parts_membership R X _ hV.1 f hf.
    have hh := hB.2 _ _ hp hq.
    rewrite /function_seminorm_distance positive_parts_difference in hh.
    exact: hh.
Qed.
