(** Federer (1969), 2.6.4, p. 119: supporting boundedness of the iterated
    Daniell functional on each fixed compact rectangle. The estimate follows
    by applying the two compact-support bounds of 2.5.13, pp. 106–107,
    successively. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactProductSections
  CompactSectionFunctional CompactDaniellUniformBound DaniellIntegralUP DaniellIntegralAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [iterated_compact_functional_fixed_support_bound]:
    supporting uniform bound on compact rectangles in the proof of
    the final proposition of Federer 2.6.4, p. 119.
    The constant is independent of the tested function. *)
Theorem iterated_compact_functional_fixed_support_bound (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) (K : set X) (L : set Y) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  compact K -> compact L ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) B ->
  exists C, 0<=C /\ forall f, compactly_supported_continuous_functions f ->
    (forall x y, ~ (K x /\ L y) -> f (x,y)=0) -> forall e, 0<e ->
    (forall x y, `|f (x,y)|<=e) -> `|B (fun y => A (fun x => f (x,y)))|<=e*C.
Proof.
move=> hX hlX hY hlY hK hL hA hB.
have [CA [hCA hAb]] := @compact_daniell_fixed_support_bound R X A K hX hlX hK hA.
have [CB [hCB hBb]] := @compact_daniell_fixed_support_bound R Y B L hY hlY hL hB.
exists ((CA+1)*CB); split.
- exact (mulr_ge0 (addr_ge0 hCA ler01) hCB).
- move=> f hf hz e he hfe.
  have hg := @compact_section_functional_compact_support R X Y A f hX hlX hY hA hf.
  have hgz y : ~L y -> A (fun x => f (x,y))=0.
    move=> hy; have hz' : (fun x => f (x,y))=(fun _ => (0 : R)).
      apply: funext=> x; apply: (@hz x y). move=> [_ hly]; exact: hy hly.
    rewrite hz'; exact (@daniell_integral_zero R X _ A hA _ (@compactly_supported_zero_function R X)).
  have hval y : `|A (fun x => f (x,y))|<=e*CA.
    apply: (@hAb (fun x => f (x,y)) (@compact_product_first_section R X Y f y hX hf) _ e he).
    + move=> x hx; apply: (@hz x y). move=> [hk _]; exact: hx hk.
    + move=> x _; exact: hfe.
  have hCA1 : 0<CA+1.
    have hh : CA<CA+1 by rewrite ltrDl ltr01.
    exact: le_lt_trans hCA hh.
  have hep : 0<e*(CA+1) := mulr_gt0 he hCA1.
  have hbnd := @hBb (fun y => A (fun x => f (x,y))) hg hgz (e*(CA+1)) hep.
  rewrite mulrA; apply: hbnd=> y _.
  have hh : CA<=CA+1 by rewrite lerDl ler01.
  exact (le_trans (hval y) (ler_wpM2l (ltW he) hh)).
Qed.
