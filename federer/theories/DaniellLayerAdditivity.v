(** Federer (1969), proof of 2.5.2, p. 93: summing the layer inequalities
    and telescoping both the functional and integral terms. The nonnegative
    integral values may still be infinite; their addition is always defined. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws FunctionLatticeLayers MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverMeasure DaniellPositiveIntegral SummableRealFunctionUP
  ExtendedRealPartial MeasureIntegralUP MeasureIntegralBounds MeasureIntegralAddition
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureFiniteRealSumIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_layer_functional_add]: telescoping adjacent
    functional values in Federer 2.5.2, p. 93 Ordered subtraction provides
    membership of every layer. *)
Lemma daniell_layer_functional_add (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (f : X -> R) a b c :
  L f -> (0 <= a)%R -> (a <= b)%R -> (b <= c)%R ->
  A (real_lattice_layer f a c)=(A (real_lattice_layer f a b)+A (real_lattice_layer f b c))%R.
Proof.
move=> hf ha hab hbc.
have hl := (real_lattice_layer_member hL hf ha hab).1.
have hr := (real_lattice_layer_member hL hf (le_trans ha hab) hbc).1.
have he : (fun x => (real_lattice_layer f a b x+real_lattice_layer f b c x)%R)=real_lattice_layer f a c.
  apply: funext=> x; exact: real_lattice_layer_telescope.
have hh := @monotone_daniell_integral_add R X L A hA _ _ hl hr.
by rewrite he in hh.
Qed.

(** Source for [daniell_layer_integral_add]: telescoping the integral terms
    in Federer 2.5.2, p. 93 Positivity ensures defined addition even before
    finiteness has been proved. *)
Lemma daniell_layer_integral_add (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) (f : X -> R) a b c :
  L f -> (0 <= a)%R -> (a <= b)%R -> (b <= c)%R ->
  measure_lower_integral mu (real_total_integrand (real_lattice_layer f a c))=
  measure_lower_integral mu (real_total_integrand (real_lattice_layer f a b))+
  measure_lower_integral mu (real_total_integrand (real_lattice_layer f b c)).
Proof.
move=> hf ha hab hbc.
have hmeasure := daniell_cover_is_measure hL hA hm (function_lattice_zero hL hf).
have hl := real_lattice_layer_member hL hf ha hab.
have hr := real_lattice_layer_member hL hf (le_trans ha hab) hbc.
have hs := real_lattice_layer_member hL hf ha (le_trans hab hbc).
have [hil hpl] := daniell_positive_lattice_integral hL hA hm hl.
have [hir hpr] := daniell_positive_lattice_integral hL hA hm hr.
have his := (daniell_positive_lattice_integral hL hA hm hs).1.
pose u := measure_lower_integral mu (real_total_integrand (real_lattice_layer f a b)).
pose v := measure_lower_integral mu (real_total_integrand (real_lattice_layer f b c)).
have hadd : extended_add u v=Some (u+v).
  by rewrite /extended_add (ge0_adde_def hpl hpr).
have hi := @measure_integral_add R X mu hmeasure _ _ u v (u+v) hil hir hadd.
have he := real_total_sum_embedding_graph (real_lattice_layer f a b) (real_lattice_layer f b c).
have hh := measure_integral_graph_equivalent he hi.
have hfun : (fun x => (real_lattice_layer f a b x+real_lattice_layer f b c x)%R)=real_lattice_layer f a c.
  apply: funext=> x; exact: real_lattice_layer_telescope.
rewrite hfun in hh; exact: measure_integral_unique his hh.
Qed.
