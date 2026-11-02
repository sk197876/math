(** Federer (1969), 2.6.4, p. 119, final proposition: applying a Daniell
    functional to the first-variable sections gives a member of K(Y). This
    supporting construction uses local uniform continuity over the projected
    compact support and the order bounds of 2.5.13, pp. 106–107. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground FunctionLatticeUP FunctionLatticeSeminormUP
  DaniellIntegralUP DaniellIntegralAlgebra CompactSupportFunctionUP CompactSupportFunctionLattice
  DaniellSpaceCompactness CompactProductSections CompactSectionUniform CompactDaniellUniformBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_section_functional_continuous]: supporting
    continuity of y maps to lambda(h(.,y)) in the final
    proposition of Federer 2.6.4, p. 119. *)
Theorem compact_section_functional_continuous (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (h : (X*Y) -> R) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  compactly_supported_continuous_functions h ->
  continuous (fun y : Y => (A (fun x => h (x,y)) : real_line_metric R)).
Proof.
move=> hh hl hA hhf.
pose K := fst @` real_function_support h.
have hK : compact K := compact_product_first_projection hhf.2.
have [C [hC hbound]] := @compact_daniell_fixed_support_bound R X A K hh hl hK hA.
have hc y := @compact_product_first_section R X Y h y hh hhf.
have hz y x : ~K x -> h (x,y)=0.
  move=> hx; apply: real_function_zero_off_support=> hp; apply: hx; exists (x,y)=> //.
have hlin := @daniell_compact_support_linear R X A hA.
move=> b; apply/cvg_ballP=> e he.
have hC1 : C<C+1 by rewrite ltrDl ltr01.
have hden : 0<C+1 := le_lt_trans hC hC1.
pose d := e/(C+1).
have hd : 0<d by rewrite /d divr_gt0.
have [V [hV [hb hnear]]] := @compact_sections_locally_uniform R X Y h K b d hhf.1 hK hd.
have hnb : nbhs b V by rewrite openE in hV; exact: hV b hb.
apply: (@filterS _ _ (@nbhs_filter Y b) V _ _ hnb)=> y hy.
pose f x := h (x,y)-h (x,b).
have hf : compactly_supported_continuous_functions f.
  exact (@function_lattice_add R X _ (@compactly_supported_continuous_functions_lattice R X)
    _ _ (hc y) (@compactly_supported_opp R X _ (hc b))).
have hfz x : ~K x -> f x=0 by move=> hx; rewrite /f (hz y x hx) (hz b x hx) subrr.
have hfe x : K x -> `|f x|<=d by move=> hx; exact: ltW (hnear y x hy hx).
have hbnd := hbound f hf hfz d hd hfe.
have hv : A f=A (fun x => h (x,y))-A (fun x => h (x,b)).
  rewrite /f (hlin.1 _ _ (hc y) (@compactly_supported_opp R X _ (hc b))).
  by rewrite (@daniell_compact_support_opp R X A _ hA (hc b)).
have hde : d*C<e.
  have hm : d*C<d*(C+1) by rewrite ltr_pM2l // ltrDl ltr01.
  by rewrite /d divfK ?gt_eqF // in hm.
rewrite /ball /= distrC; rewrite hv in hbnd; exact: le_lt_trans hbnd hde.
Qed.

(** Source for [compact_section_functional_compact_support]: supporting
    membership in K(Y) of the iterated functional's intermediate
    function in Federer 2.6.4, p. 119. It vanishes
    outside the second projection of the original support. *)
Theorem compact_section_functional_compact_support (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (h : (X*Y) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  compactly_supported_continuous_functions h ->
  compactly_supported_continuous_functions (fun y => A (fun x => h (x,y))).
Proof.
move=> hh hl hY hA hf; split.
- exact (@compact_section_functional_continuous R X Y A h hh hl hA hf).
- have hK := compact_product_second_projection hf.2.
  apply: (@real_function_compact_support_in_closed_set R Y _ (snd @` real_function_support h)
    hK (compact_closed hY hK))=> y hy.
  have hz : (fun x => h (x,y))=(fun _ => (0 : R)).
    apply: funext=> x; apply: real_function_zero_off_support=> hp; apply: hy; exists (x,y)=> //.
  rewrite hz; exact (@daniell_integral_zero R X _ A hA _ (@compactly_supported_zero_function R X)).
Qed.
