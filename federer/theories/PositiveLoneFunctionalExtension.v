(** Federer (1969), 2.5.9, p. 100: extend first from L+ to total L1+, as
    required by erratum p. 2, book p. 100 line 22. The scalar extension is
    obtained only through its sealed agreement and Lipschitz laws. Density
    proves additivity and positive homogeneity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP FunctionLatticeUP FunctionLatticeLaws FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralAlgebra RealIntegralFunctionalUP RegularDaniellEnvelope
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm
  ScalarLipschitzExtensionUP ScalarLipschitzExtension FunctionSeminormDistance
  DenseScalarExtensionAddition DenseScalarExtensionScaling RegularLatticeLoneDensity DominatedLatticeLoneLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_lone_functional_extension_exists]:
    corrected positive-cone extension in Federer 2.5.9, p. 100,
    erratum p. 2 line 22. The original lattice need not be a
    vector space. Its regular representing measure supplies nonemptiness. *)
Theorem positive_lone_functional_extension_exists (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_function_lattice_regular L mu -> is_daniell_integral L A ->
  (forall f, L f -> (`|A f| <= F (fun x => `|f x|))%R) ->
  exists B : (X -> R) -> R,
    is_scalar_lipschitz_extension (positive_function_lattice (total_scalar_lp mu 1))
      (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) A B /\
    B (fun _ => 0%R)=0%R /\
    (forall f g, positive_function_lattice (total_scalar_lp mu 1) f ->
      positive_function_lattice (total_scalar_lp mu 1) g ->
      B (fun x => (f x+g x)%R)=(B f+B g)%R) /\
    (forall c f, (0 <= c)%R -> positive_function_lattice (total_scalar_lp mu 1) f ->
      B (fun x => (c*f x)%R)=(c*B f)%R).
Proof.
move=> hF hrepr hr hA hb.
pose V := total_scalar_lp mu 1.
pose W := positive_function_lattice V.
pose D := positive_function_lattice L.
pose N := finite_total_scalar_lp_norm mu 1.
pose d := function_seminorm_distance N.
have hV := @total_scalar_lp_vector_lattice R X mu hm 1 (lexx _).
have hW := @positive_function_lattice_laws R X V hV.1.
have hD := @positive_function_lattice_laws R X L hL.
have hfull := @function_seminorm_distance_laws R X V N hV
  (@finite_total_scalar_lp_norm_laws R X mu hm 1).
have hd : is_pseudometric_on_set W d.
  split; first by move=> f g hf hg; exact: hfull.1 f g hf.1 hg.1.
  split; first by move=> f hf; exact: hfull.2.1 f hf.1.
  split.
  - by move=> f g hf hg; exact: hfull.2.2.1 f g hf.1 hg.1.
  - by move=> f g h hf hg hh; exact: hfull.2.2.2 f g h hf.1 hg.1 hh.1.
have hDW : forall f, D f -> W f.
  move=> f hf; split.
  - exact: (@represented_lattice_in_total_lone R X mu hm L F hrepr f hf.1).
  - exact: hf.2.
have [u hu] := @function_lattice_regular_nonempty R X L mu hm hr.
have hzero : D (fun _ => 0%R).
  split; first exact: (@function_lattice_zero R X L hL u hu).
  by move=> x.
have hne : exists f, D f by exists (fun _ => 0%R).
have hAd : is_scalar_lipschitz_on_set D d A.
  move=> f g hf hg; exact: (@dominated_lattice_lone_lipschitz R X L hL F A mu hm hF hrepr hA hb f g hf.1 hg.1).
pose B := @scalar_lipschitz_extension R (X -> R) W D d A hd hDW hne hAd.
have hB := @scalar_lipschitz_extension_specification R (X -> R) W D d A hd hDW hne hAd.
have hdense := @regular_positive_lattice_lone_dense R X L F hL mu hm hrepr hr.
exists B; split=> //.
have hB0 : B (fun _ => 0%R)=0%R.
  rewrite /B (hB.1 _ hzero); exact: (@daniell_integral_zero R X L A hA u hu).
split=> //; split.
- apply: (@dense_scalar_extension_additive R (X -> R) W D d (fun f g x => (f x+g x)%R) A B hd hDW hdense).
  + exact: (@function_lattice_add R X W hW).
  + exact: (@function_lattice_add R X D hD).
  + move=> f g h hf hg hh; rewrite /d function_seminorm_distance_translate_right; exact: lexx.
  + move=> f g h hf hg hh; rewrite /d function_seminorm_distance_translate_left; exact: lexx.
  + move=> f g hf hg; exact: (@daniell_integral_add R X L A hA f g hf.1 hg.1).
  + exact: hB.
- move=> c f hc hf; case: (eqVneq c 0%R)=> [->|hc0].
  + have he : (fun x : X => (0*f x)%R)=(fun _ => 0%R) by apply: funext=> x; rewrite mul0r.
    by rewrite he hB0 mul0r.
  + have hcpos : (0 < c)%R by rewrite lt_neqAle eq_sym hc0 hc.
    apply: (@dense_scalar_extension_positive_scaling R (X -> R) W D d
      (fun g x => (c*g x)%R) A B c hd hDW hdense hcpos).
    * move=> g hg; exact: (@function_lattice_scale R X W hW c g hc hg).
    * move=> g hg; exact: (@function_lattice_scale R X D hD c g hc hg).
    * move=> g h hg hh; rewrite /d (@function_seminorm_distance_scale R X V N hV
        (@finite_total_scalar_lp_norm_laws R X mu hm 1) c g h hg.1 hh.1) (ger0_norm hc).
      exact: lexx.
    * move=> g hg; exact: (@daniell_integral_scale R X L A hA c g hc hg.1).
    * exact: hB.
    * exact: hf.
Qed.
