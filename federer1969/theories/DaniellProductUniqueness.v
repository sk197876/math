(** Federer (1969), 2.6.4, p. 119: uniqueness of the Daniell functional on
    K(X times Y) with the prescribed separated-product values. Uniform
    finite separated approximation with a common compact support proves
    uniqueness even for signed functionals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeSeminormUP DaniellIntegralUP DaniellSpaceCompactness
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactProductSections CompactSeparatedProduct
  CompactCutoffUP CompactCutoff CompactDaniellUniformBound CompactProductApproximationUP
  CompactProductApproximationSealed CompactSeparatedSumLaws DaniellProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_daniell_separated_values_determine]:
    uniqueness argument for the final proposition in Federer
    2.6.4, p. 119. Equality is asserted on K(X times Y),
    the actual domain in the book. *)
Theorem compact_daniell_separated_values_determine (R : realType) (X Y : topologicalType)
    (C D : ((X*Y) -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) C ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) D ->
  (forall f g, compactly_supported_continuous_functions f -> compactly_supported_continuous_functions g ->
    C (fun p : X*Y => f p.1*g p.2)=D (fun p : X*Y => f p.1*g p.2)) ->
  forall h, compactly_supported_continuous_functions h -> C h=D h.
Proof.
move=> hX hlX hY hlY hC hD hagree h hh.
pose K := fst @` real_function_support h.
pose L := snd @` real_function_support h.
have hK : compact K := compact_product_first_projection hh.2.
have hL : compact L := compact_product_second_projection hh.2.
have hz x y : ~(K x /\ L y) -> h (x,y)=0.
  move=> hn; apply: real_function_zero_off_support=> hs; apply: hn; split; by exists (x,y).
pose v := @compact_cutoff R Y L hY hlY hL.
have hv := @compact_cutoff_specification R Y L hY hlY hL.
pose S := real_function_support v.
have hS : compact S := (compact_cutoff_function hv).2.
pose u := @compact_cutoff R X K hX hlX hK.
have hu := @compact_cutoff_specification R X K hX hlX hK.
pose t := @compact_cutoff R Y S hY hlY hS.
have ht := @compact_cutoff_specification R Y S hY hlY hS.
pose w (p : X*Y) := u p.1*t p.2.
have hwp : positive_function_lattice (@compactly_supported_continuous_functions R (X*Y)%type) w.
  split; first exact (@compactly_supported_separated_product R X Y u t
    (compact_cutoff_function hu) (compact_cutoff_function ht)).
  move=> [x y]; exact (mulr_ge0 (andP (compact_cutoff_range hu x)).1 (andP (compact_cutoff_range ht y)).1).
have [c [hc hCb]] := @compact_daniell_scaled_order_bound R (X*Y)%type C w hC hwp.
have [d [hd hDb]] := @compact_daniell_scaled_order_bound R (X*Y)%type D w hD hwp.
have hlinC := @daniell_compact_support_linear R (X*Y)%type C hC.
have hlinD := @daniell_compact_support_linear R (X*Y)%type D hD.
have hbound e : 0<e -> `|C h-D h|<=e*(c+d).
  move=> he.
  have [q [hq [hqz herror]]] := @CompactProductApproximation.exists_approximation R X Y h K L v e
    hX hY hlY hh hK hz hv he.
  have hqm := @finite_compact_separated_sum_member R X Y q hq.
  have hqd := @compact_daniell_agree_finite_separated_sums R X Y C D hC hD hagree q hq.
  pose f p := h p-q p.
  have hf : compactly_supported_continuous_functions f.
    exact (@function_lattice_add R (X*Y)%type _ (@compactly_supported_continuous_functions_lattice R (X*Y)%type)
      _ _ hh (@compactly_supported_opp R (X*Y)%type q hqm)).
  have hfw p : `|f p|<=e*w p.
    case: p=> x y; case: (pselect (K x /\ S y))=> [[hx hy]|hn].
    - rewrite /w /= /u /t (compact_cutoff_on_set hu hx) (compact_cutoff_on_set ht hy) !mulr1.
      exact: herror (x,y).
    - have hhz : h (x,y)=0.
        apply: (@hz x y). move=> [hx hly]; apply: hn; split=> //.
        apply: (@subset_closure Y [set z | v z<>0] y).
        change (v y<>0); rewrite /v (compact_cutoff_on_set hv hly); by move/eqP; rewrite oner_eq0.
      rewrite /f hhz (hqz x y hn) subrr normr0; exact: mulr_ge0 (ltW he) (hwp.2 (x,y)).
  have hcbd := @hCb f hf e he hfw.
  have hdbd := @hDb f hf e he hfw.
  have hvC : C f=C h-C q.
    rewrite /f (hlinC.1 _ _ hh (@compactly_supported_opp R (X*Y)%type q hqm)).
    by rewrite (@daniell_compact_support_opp R (X*Y)%type C q hC hqm).
  have hvD : D f=D h-D q.
    rewrite /f (hlinD.1 _ _ hh (@compactly_supported_opp R (X*Y)%type q hqm)).
    by rewrite (@daniell_compact_support_opp R (X*Y)%type D q hD hqm).
  have heq : C h-D h=C f-D f by rewrite hvC hvD hqd opprB addrA subrK.
  rewrite heq mulrDr; exact: le_trans (ler_normB _ _) (lerD hcbd hdbd).
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT leNgt; apply/negP=> hp.
have hcd : 0<=c+d := addr_ge0 hc hd.
have hc1 : c+d<c+d+1 by rewrite ltrDl ltr01.
have hden : 0<c+d+1 := le_lt_trans hcd hc1.
pose e := `|C h-D h|/(c+d+1).
have he : 0<e by rewrite /e divr_gt0.
have hhbound := hbound e he.
have hlt : e*(c+d)<`|C h-D h|.
  have hm : e*(c+d)<e*(c+d+1) by rewrite ltr_pM2l.
  by rewrite /e divfK ?gt_eqF // in hm.
have hh' := le_lt_trans hhbound hlt; by rewrite ltxx in hh'.
Qed.

(** Source for [daniell_product_unique]: exact uniqueness conclusion
    for the last product-functional diagram of Federer 2.6.4,
    p. 119. Values outside K(X times Y) are immaterial. *)
Theorem daniell_product_unique (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R) (C D : ((X*Y) -> R) -> R) :
  hausdorff_space X -> locally_compact (@setT X) -> hausdorff_space Y -> locally_compact (@setT Y) ->
  is_daniell_product A B C -> is_daniell_product A B D ->
  forall h, compactly_supported_continuous_functions h -> C h=D h.
Proof.
move=> hX hlX hY hlY hC hD.
apply: (@compact_daniell_separated_values_determine R X Y C D hX hlX hY hlY hC.1 hD.1).
move=> f g hf hg; by rewrite (hC.2 f g hf hg) (hD.2 f g hf hg).
Qed.
