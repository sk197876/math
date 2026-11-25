(** Federer (1969), 4.1.5, pp. 349–350: finite
    original gauge gives finite scalar limits for
    compact uniform test approximations. Uniformly zero
    approximations have zero limit. The actual localized
    cutoff discharges all quantitative gauge premises. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP CompactCutoffUP
  LocalizedCompactCutoffUP CompactUniformApproximationUP DistributionVariationUP
  DistributionFiniteGaugeCutoff DistributionVariationCauchy DistributionVariationUniformZero PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionCompactUniformLimits.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Hypothesis hh:hausdorff_space X.
Hypothesis hl:locally_compact (@setT X).
Hypothesis hU:open U.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.
Hypothesis hFinite:forall f:X->R,
  @positive_function_lattice R X (@compactly_supported_continuous_functions R X) f ->
  @real_function_support R X f `<=` U ->
  exists b:R,is_distribution_variation_value NY value S f b%:E.
Local Notation A := (@is_compact_uniform_test_approximation R X U Y NY E value).

(** Source for [distribution_compact_uniform_limit_exists]:
    the finite convolution-limit argument of Federer
    4.1.5, p. 349, for any actual test approximation
    with the same proved uniform and support properties. *)
Theorem distribution_compact_uniform_limit_exists w P:
  A w P ->exists t:R,positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) t.
Proof.
move=>[C [hC [hCU [r [hr [hOff hApprox]]]]]].
have[g [b [hG hGauge]]]:=@distribution_finite_gauge_cutoff R X U Y NY E value S
  hh hl hU hFinite C hC hCU.
have hNonnegative:function_nonnegative g.
  move=>x; exact:(andP (compact_cutoff_range (localized_compact_cutoff_laws hG) x)).1.
exact:(@distribution_variation_approximation_limit R X Y NY hNY E value S P w C g b r
  hr hNonnegative (fun x hx=>compact_cutoff_on_set (localized_compact_cutoff_laws hG) hx)
  hGauge hOff hApprox).
Qed.

(** Source for [distribution_compact_uniform_zero_limit]:
    the original finite-gauge estimate sends common-
    support uniformly vanishing tests to zero, supporting
    linearity and independence of T in Federer 4.1.5,
    pp. 349–350. *)
Theorem distribution_compact_uniform_zero_limit P:
  A (fun _=>0) P ->
  positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) 0.
Proof.
move=>[C [hC [hCU [r [hr [hOff hApprox]]]]]].
have[g [b [hG hGauge]]]:=@distribution_finite_gauge_cutoff R X U Y NY E value S
  hh hl hU hFinite C hC hCU.
have hNonnegative:function_nonnegative g.
  move=>x; exact:(andP (compact_cutoff_range (localized_compact_cutoff_laws hG) x)).1.
have hUniform eta:0<eta ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->forall x,NY (value (P e) x)<eta.
  move=>hEta; have[d [hd hBound]]:=hApprox eta hEta.
  exists d; split=>// e he hed x.
  have hB:=hBound e he hed x; by rewrite subr0 in hB.
exact:(@distribution_variation_uniform_zero_limit R X Y NY hNY E value S P C g b r
  hr hNonnegative (fun x hx=>compact_cutoff_on_set (localized_compact_cutoff_laws hG) hx)
  hGauge hOff hUniform).
Qed.
End DistributionCompactUniformLimits.
