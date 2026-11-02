(** Federer (1969), 1.7.9, p. 35: the product of the exterior powers of two
    maps is the trace of the exterior power of their adjoint composite. The
    book states positive degrees; our statement also includes degree zero,
    where the exterior maps are the identity on scalars. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorPositivity
  ExteriorMaps ExteriorGrading ExteriorMapScaling ExteriorAdjoint
  FiniteExteriorPowers ExteriorIndices FiniteOrdinalBasis LinearBasis
  HomInner HomInnerTrace Hom TensorUP AdjointUP Adjoint
  GammaIntrinsic GammaPower TraceDefinition TracePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Exterior.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.

(** Source for [exterior_hom_inner]: Federer 1.7.9, p. 35,
    the product of degree-m maps as elements of the corresponding
    Hom space, using the induced exterior inner products. *)
Definition exterior_hom_inner m := hom_inner
  (@exterior_inner_productP R h2 V B hB m)
  (@exterior_inner_productP R h2 W C hC m)
  (finite_ordinal_basis (@finite_e_lambda_basis R n V b hb h2 m)).
Arguments exterior_hom_inner m _ _ : clear implicits.

(** Source for [exterior_hom_adjoint_trace]: Federer 1.7.9,
    p. 35, second displayed trace formula: the product of the
    exterior maps of f and g is trace of the exterior map of
    a composed with g, whenever a is adjoint to f. *)
Theorem exterior_hom_adjoint_trace m (f g : {linear V -> W})
    (a : {linear W -> V}) (ha : is_adjoint B C f a) :
  exterior_hom_inner m (hom_of_linear (exterior_power_map f m))
    (hom_of_linear (exterior_power_map g m)) =
  trace h2 V (@Gamma_power_A R h2 V V n b hb m
    (hom_of_linear (exterior_power_map (linear_comp a g) m))).
Proof.
rewrite /exterior_hom_inner.
have hx := @hom_inner_adjoint_trace R h2 (exterior_power V m) (exterior_power W m)
  _ _ (@exterior_inner_productP R h2 V B hB m)
  (@exterior_inner_productP R h2 W C hC m)
  #|{:Lambda n m}| _ (finite_ordinal_basis (@finite_e_lambda_basis R n V b hb h2 m))
  (hom_of_linear (exterior_power_map f m)) (hom_of_linear (exterior_power_map g m))
  (exterior_power_map a m) (@exterior_power_adjoint R h2 V W B C hB hC f a ha m).
rewrite hx trace_Gamma_power.
have hc : hom_of_linear (linear_comp (exterior_power_map a m)
    (hom_as_linear (hom_of_linear (exterior_power_map g m)))) =
    hom_of_linear (exterior_power_map (linear_comp a g) m).
  apply: hom_ext => x; change (exterior_power_map a m (exterior_power_map g m x) = exterior_power_map (linear_comp a g) m x).
  exact: exterior_power_map_composition.
rewrite hc.
exact: trace_basis_independent.
Qed.

(** Source for [exterior_hom_inner_trace]: Federer 1.7.9,
    p. 35, the exterior trace identity with the canonical adjoint. *)
Theorem exterior_hom_inner_trace m (f g : {linear V -> W}) :
  exterior_hom_inner m (hom_of_linear (exterior_power_map f m))
    (hom_of_linear (exterior_power_map g m)) =
  trace h2 V (@Gamma_power_A R h2 V V n b hb m
    (hom_of_linear (exterior_power_map (linear_comp (inner_adjoint hB hC hb f) g) m))).
Proof. exact: exterior_hom_adjoint_trace (inner_adjointP hB hC hb f). Qed.
End Exterior.

Arguments exterior_hom_inner {R} h2 {V W B C} hB hC {n b} hb m _ _.
