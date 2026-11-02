(** Private approximation proof supporting Federer (1969), 2.6.4, p. 119:
    finite sums of separated compactly supported continuous functions
    approximate h uniformly with a common compact support. it does not state
    this approximation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportProducts CompactProductSections
  CompactSectionUniform CompactFiniteCover CompactCutoffUP FiniteCompactPartitionUP FiniteCompactPartitionSealed
  CompactProductApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_separated_approximation_exists]:
    supporting fixed-support approximation for uniqueness in the final
    proposition of Federer 2.6.4, p. 119. The output
    support lies in K times support(v), independently of epsilon. *)
Theorem compact_product_separated_approximation_exists (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) (K : set X) (L : set Y) (v : Y -> R) (e : R) :
  hausdorff_space X -> hausdorff_space Y -> locally_compact (@setT Y) ->
  compactly_supported_continuous_functions h -> compact K ->
  (forall x y, ~(K x /\ L y) -> h (x,y)=0) -> is_compact_cutoff L v -> 0<e ->
  exists q : (X*Y) -> R, is_finite_compact_separated_sum q /\
    (forall x y, ~(K x /\ real_function_support v y) -> q (x,y)=0) /\
    forall p, `|h p-q p|<=e.
Proof.
move=> hX hY hlY hh hK hz hv he.
pose S := real_function_support v.
have hS : compact S := (compact_cutoff_function hv).2.
have hnear y : exists V : set Y, open V /\ V y /\ forall z x, V z -> K x -> `|h (x,z)-h (x,y)|<e.
  exact (@compact_sections_locally_uniform R X Y h K y e hh.1 hK he).
pose V y := sval (cid (hnear y)).
have hV y := svalP (cid (hnear y)).
have hcov : S `<=` \bigcup_(y in setT) V y.
  move=> y hy; exists y=> //; exact: (hV y).2.1.
have [F hF hcover] := @compact_open_finite_cover Y Y setT V S hS (fun y _ => (hV y).1) hcov.
have hVo j : j \in F -> open (V j) by move=> _; exact: (hV j).1.
pose g := @FiniteCompactPartition.value R Y Y V F S hY hlY hS hVo hcover.
have hg := @FiniteCompactPartition.laws R Y Y V F S hY hlY hS hVo hcover.
pose a j x := h (x,j).
pose b j y := g j y*v y.
pose q (p : X*Y) := \sum_(j <- F) a j p.1*b j p.2.
have hgp j hj := @finite_compact_partition_functions R Y Y V F S g hg j hj.
have hgr j hj y := @finite_compact_partition_range R Y Y V F S g hg j hj y.
have hvs y := compact_cutoff_range hv y.
have hzero x y : ~K x -> h (x,y)=0.
  move=> hx; apply: (@hz x y); by move=> [hk _]; apply: hx.
have hqzero x y : ~(K x /\ S y) -> q (x,y)=0.
  move=> hn; rewrite /q; apply: big1=> j hj; rewrite /a /b /=.
  case: (pselect (K x))=> hx.
  - have hy : ~S y by move=> hy; apply: hn; split.
    by rewrite (real_function_zero_off_support hy) !mulr0.
  - by rewrite (hzero x j hx) mul0r.
exists q; split.
- exists F,a,b; split=> // j hj; split.
  + exact (@compact_product_first_section R X Y h j hX hh).
  + exact (@compact_support_continuous_multiplier R Y (g j) v (hgp j hj).1 (compact_cutoff_function hv)).
split=> // p; case: p=> x y /=.
case: (pselect (K x /\ S y))=> [[hx hy]|hn].
- have hsum : \sum_(j <- F) g j y = 1 := @finite_compact_partition_sum R Y Y V F S g hg y hy.
  have hmult : h (x,y)*v y=h (x,y).
    case: (pselect (L y))=> hly.
    + by rewrite (compact_cutoff_on_set hv hly) mulr1.
    + have hh0 : h (x,y)=0.
        apply: (@hz x y); by move=> [_ hl]; apply: hly.
      by rewrite hh0 mul0r.
  have herr : h (x,y)-q (x,y)=\sum_(j <- F) (h (x,y)-h (x,j))*g j y*v y.
    rewrite /q /a /b /=.
    transitivity ((\sum_(j <- F) h (x,y)*g j y*v y)-\sum_(j <- F) h (x,j)*(g j y*v y)).
    + by rewrite -mulr_suml -mulr_sumr hsum mulr1 hmult.
    + rewrite -sumrB; apply: eq_bigr=> j hj; by rewrite !mulrBl mulrA.
  rewrite herr; apply: le_trans (ler_norm_sum _ _ _) _.
  have hterm j : j \in F -> `|(h (x,y)-h (x,j))*g j y*v y|<=e*g j y*v y.
    move=> hj; rewrite !normrM (ger0_norm (andP (hgr j hj y)).1) (ger0_norm (andP (hvs y)).1).
    case: (eqVneq (g j y) 0)=> hg0; first by rewrite hg0 !mulr0 !mul0r.
    have hsy : real_function_support (g j) y by apply: subset_closure=> hh0; apply: (negP hg0); apply/eqP.
    have hvy := @finite_compact_partition_support R Y Y V F S g hg j hj y hsy.
    have hdiff := ltW ((hV j).2.2 y x hvy hx).
    exact (ler_wpM2r (andP (hvs y)).1 (ler_wpM2r (andP (hgr j hj y)).1 hdiff)).
  have hsumle : (\sum_(j <- F) `|(h (x,y)-h (x,j))*g j y*v y|)<=\sum_(j <- F) e*g j y*v y.
    rewrite !big_seq; apply: ler_sum=> j hj; exact: hterm j hj.
  apply: le_trans hsumle _.
  rewrite -mulr_suml -mulr_sumr hsum mulr1.
  have hb := ler_wpM2l (ltW he) (andP (hvs y)).2; by rewrite mulr1 in hb.
- rewrite (hqzero x y hn) subr0.
  have hh0 : h (x,y)=0.
    case: (pselect (K x))=> hx; last exact: hzero x y hx.
    apply: (@hz x y). move=> [_ hly]; apply: hn; split=> //.
    apply: (@subset_closure Y [set z | v z<>0] y).
    change (v y<>0); rewrite (compact_cutoff_on_set hv hly); by move/eqP; rewrite oner_eq0.
  rewrite hh0 normr0; exact: ltW he.
Qed.
