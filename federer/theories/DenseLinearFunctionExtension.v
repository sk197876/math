(** Federer (1969), 2.6.6, p. 120: the norm-bounded linear functional on the
    dense union L extends uniquely to K(X). This supporting lemma derives
    linearity from the sealed scalar Lipschitz extension and density. It
    does not assume completeness of the function space. Source context:
    UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import FunctionLatticeUP LatticeAdditiveFunctional VectorFunctionLattice FunctionLatticeSeminormUP FunctionSeminormUnitBound
  FunctionSeminormDistance ScalarLipschitzExtensionUP ScalarLipschitzExtension
  DenseScalarExtensionAddition DenseScalarExtensionScaling DenseScalarExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_linear_function_extension_exists]: the linear
    extension step in Federer 2.6.6, p. 120, with an explicit
    seminorm and its density hypothesis. Existence is proved, not
    posited. This general lemma is also usable for the inverse-limit
    paragraph on pp. 120–121. *)
Theorem dense_linear_function_extension_exists (R : realType) (X : Type)
    (W D : set (X -> R)) (N A : (X -> R) -> R) :
  is_vector_function_lattice W -> is_vector_function_lattice D ->
  (forall f, D f -> W f) -> is_finite_function_seminorm W N ->
  is_pseudometric_dense_subset W D (function_seminorm_distance N) ->
  is_linear_functional_on_functions D A -> (forall f, D f -> `|A f|<=N f) ->
  exists B, is_linear_functional_on_functions W B /\
    is_scalar_lipschitz_extension W D (function_seminorm_distance N) A B /\
    forall f, W f -> `|B f|<=N f.
Proof.
move=> hW hD hDW hN hdense hA hb.
pose d := function_seminorm_distance N.
have hd := @function_seminorm_distance_laws R X W N hW hN.
have hne : exists f, D f by exists (fun _=>0); exact: hD.2.1.
have hAd : is_scalar_lipschitz_on_set D d A.
  move=> f g hf hg; rewrite -(@vector_lattice_additive_difference R X D A hD hA.1 f g hf hg).
  exact: hb _ (@vector_function_lattice_difference R X D hD f g hf hg).
pose B := @scalar_lipschitz_extension R (X -> R) W D d A hd hDW hne hAd.
have hB := @scalar_lipschitz_extension_specification R (X -> R) W D d A hd hDW hne hAd.
have hB0 : B (fun _=>0)=0.
  rewrite /B (hB.1 _ hD.2.1); exact: (@lattice_additive_zero R X D A hD.1 hA.1 _ hD.2.1).
have hadd : forall f g, W f -> W g -> B (fun x=>f x+g x)=B f+B g.
  apply: (@dense_scalar_extension_additive R (X -> R) W D d (fun f g x=>f x+g x) A B hd hDW hdense).
  - exact: (@function_lattice_add R X W hW.1).
  - exact: (@function_lattice_add R X D hD.1).
  - move=> f g h hf hg hh; rewrite /d function_seminorm_distance_translate_right; exact: lexx.
  - move=> f g h hf hg hh; rewrite /d function_seminorm_distance_translate_left; exact: lexx.
  - exact: hA.1.
  - exact: hB.
have hpos : forall c f, 0<c -> W f -> B (fun x=>c*f x)=c*B f.
  move=> c f hc hf.
  apply: (@dense_scalar_extension_positive_scaling R (X -> R) W D d
    (fun g x=>c*g x) A B c hd hDW hdense hc).
  - exact: hW.2.2 c.
  - exact: hD.2.2 c.
  - move=> g h hg hh; rewrite /d (@function_seminorm_distance_scale R X W N hW hN c g h hg hh)
      (ger0_norm (ltW hc)); exact: lexx.
  - exact: hA.2 c.
  - exact: hB.
  - exact: hf.
have hneg : forall f, W f -> B (fun x=> -f x)= -B f.
  exact: (@vector_lattice_additive_negation R X W B hW hadd).
exists B; split.
- split=> // c f hf; case: (ltgtP c 0)=> hc.
  + have hcpos : 0 < -c by rewrite oppr_gt0.
    have hn := @hpos (-c) f hcpos hf.
    have he : (fun x=>c*f x)=(fun x=> -((-c)*f x)) by apply: funext=> x; rewrite mulNr opprK.
    have hnegative := @hneg (fun x=>(-c)*f x) (hW.2.2 (-c) f hf).
    have hval := eq_trans (congr1 B he) hnegative.
    by rewrite hn mulNr opprK in hval.
  + exact: hpos c f hc hf.
  + have he : (fun x=>c*f x)=(fun _ : X=>0) by apply: funext=> x; rewrite hc mul0r.
    by rewrite he hB0 hc mul0r.
split=> // f hf.
have hb0 := hB.2 f (fun _=>0) hf hW.2.1.
change (is_true (`|B f-B (fun _=>0)|<=d f (fun _=>0))) in hb0.
rewrite hB0 subr0 /d /function_seminorm_distance in hb0.
have he : (fun x=>f x-0)=f by apply: funext=> x; rewrite subr0.
by rewrite he in hb0.
Qed.
