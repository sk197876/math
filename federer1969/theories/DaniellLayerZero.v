(** Federer (1969), proof of 2.5.2, p. 93: the zero-term base case of the
    formal finite layer summation. zero endpoints below are supporting
    boundary identities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLayers MonotoneDaniellIntegralUP
  MonotoneDaniellIntegralLaws SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_layer_same_functional]: vanishing empty-layer value
    supporting the summation in Federer 2.5.2, p. 93 *)
Lemma daniell_layer_same_functional (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (hA : is_monotone_daniell_integral L A)
    (f : X -> R) a : L f -> A (real_lattice_layer f a a)=0%R.
Proof. move=> hf; rewrite real_lattice_layer_same; exact: (@monotone_daniell_integral_zero R X L A hA f hf). Qed.

(** Source for [real_lattice_layer_same_integral]: vanishing empty-layer
    integral supporting the summation in Federer 2.5.2, p. 93 The source
    measure need not be finite. *)
Lemma real_lattice_layer_same_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) a :
  measure_lower_integral mu (real_total_integrand (real_lattice_layer f a a))=0.
Proof.
rewrite real_lattice_layer_same.
have hi : is_measure_integral mu (real_total_integrand (fun _ : X => 0%R)) 0.
  apply: (@measure_almost_zero_integral R X mu hm (real_total_integrand (fun _ : X => 0%R))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  by apply/real_total_integrand_graph.
exact: measure_lower_integral_unique (measure_lower_integral_specification mu _) hi.2.2.
Qed.
