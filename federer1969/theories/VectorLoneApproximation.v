(** Federer (1969), 2.5.12, printed p. 105: the two triangle estimates for
    approximation by finite sums h_i y_i. We express approximation by actual
    integrals of norm errors. This supporting predicate introduces no
    completion or quotient. it has no counterpart to the vector
    representation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasurableNormedFunctionUP SummableRealFunctionUP
  SummableRealArithmetic LatticeL1ApproximationLaws SeparableVectorLone
  MeasurableTotalNormedArithmetic VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_vector_lone_approximable]: supporting formulation
    of arbitrarily small integral norm error in Federer 2.5.12,
    p. 105, for an abstract class G of approximants. *)
Definition is_vector_lone_approximable (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (phi : set X -> \bar R)
    (G : set (X -> E)) (f : X -> E) : Prop :=
  forall e : R, 0 < e -> exists v a, G v /\
    is_measure_integral phi (real_total_integrand (fun x => N (f x-v x))) a%:E /\
    a < e.

(** Source for [vector_norm_error_triangle_integral]: the
    integral triangle estimates in Federer 2.5.12, p. 105.
    The conclusion gives an actual finite integral, including
    summability of the error, rather than only an upper integral. *)
Lemma vector_norm_error_triangle_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (f g u v : X -> real_norm_metric_space hN) (a b : R) :
  is_measurable_normed_function phi (partial_function_total f) ->
  is_measurable_normed_function phi (partial_function_total g) ->
  is_measurable_normed_function phi (partial_function_total u) ->
  is_measurable_normed_function phi (partial_function_total v) ->
  is_measure_integral phi (real_total_integrand (fun x => N (f x-u x))) a%:E ->
  is_measure_integral phi (real_total_integrand (fun x => N (g x-v x))) b%:E ->
  exists c, is_measure_integral phi
    (real_total_integrand (fun x => N ((f x+g x)-(u x+v x)))) c%:E /\ c <= a+b.
Proof.
move=> hf hg hu hv hi hj.
have hfg := @measurable_normed_total_add R X E N hN phi hphi f g hf hg.
have huv := @measurable_normed_total_add R X E N hN phi hphi u v hu hv.
have hm := (@total_vector_lone_distance_integral R X E N hN phi hphi _ _ hfg huv).1.
have hs := @real_total_integral_add R X phi hphi _ _ a b hi hj.
have hb x : `|N ((f x+g x)-(u x+v x))| <= N (f x-u x)+N (g x-v x).
  rewrite (ger0_norm (real_seminorm_nonnegative hN.1 _)).
  have he : (f x+g x)-(u x+v x)=(f x-u x)+(g x-v x) by rewrite opprD addrACA.
  rewrite he; exact (@real_seminorm_triangle R E N hN.1 (f x-u x) (g x-v x)).
have [c [hc hcb]] := real_total_dominated_integral hphi hm hs hb.
exists c; split=> //; exact: le_trans (ler_norm _) hcb.
Qed.

(** Source for [vector_norm_error_transfer_integral]: the
    estimate integral nu(w-eta) <= integral nu(w-xi) +
    integral nu(xi-eta) in Federer 2.5.12, p. 105.
    Both errors are summable; measurability of the outer error
    follows from its endpoints. *)
Lemma vector_norm_error_transfer_integral (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (f g v : X -> real_norm_metric_space hN) (a b : R) :
  is_measurable_normed_function phi (partial_function_total f) ->
  is_measurable_normed_function phi (partial_function_total v) ->
  is_measure_integral phi (real_total_integrand (fun x => N (f x-g x))) a%:E ->
  is_measure_integral phi (real_total_integrand (fun x => N (g x-v x))) b%:E ->
  exists c, is_measure_integral phi
    (real_total_integrand (fun x => N (f x-v x))) c%:E /\ c <= a+b.
Proof.
move=> hf hv hi hj.
have hm := (@total_vector_lone_distance_integral R X E N hN phi hphi f v hf hv).1.
have hs := @real_total_integral_add R X phi hphi _ _ a b hi hj.
have hb x : `|N (f x-v x)| <= N (f x-g x)+N (g x-v x).
  rewrite (ger0_norm (real_seminorm_nonnegative hN.1 _)).
  have he : f x-v x=(f x-g x)+(g x-v x) by rewrite addrA subrK.
  rewrite he; exact (@real_seminorm_triangle R E N hN.1 (f x-g x) (g x-v x)).
have [c [hc hcb]] := real_total_dominated_integral hphi hm hs hb.
exists c; split=> //; exact: le_trans (ler_norm _) hcb.
Qed.

(** Source for [vector_lone_approximable_member]: zero error for
    an existing member of G, supporting Federer 2.5.12, p. 105. *)
Lemma vector_lone_approximable_member (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (G : set (X -> E)) (f : X -> E) :
  G f -> is_vector_lone_approximable N phi G f.
Proof.
move=> hf e he; exists f,0; split=> //; split=> //.
have hz : (fun x => N (f x-f x))=(fun _ : X => 0).
  by apply: funext=> x; rewrite subrr (real_seminorm_zero hN.1).
rewrite hz; exact: real_total_zero_integral hphi.
Qed.

(** Source for [vector_lone_approximable_add]: finite sums of
    scalar lattice approximations remain approximations, Federer
    2.5.12, p. 105, the second integral triangle estimate. *)
Lemma vector_lone_approximable_add (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (G : set (X -> E))
    (hG : forall u v, G u -> G v -> G (fun x => u x+v x))
    (hGA : forall u, G u -> is_measurable_normed_function phi
      (partial_function_total (u : X -> real_norm_metric_space hN)))
    (f g : X -> real_norm_metric_space hN) :
  is_measurable_normed_function phi (partial_function_total f) ->
  is_measurable_normed_function phi (partial_function_total g) ->
  is_vector_lone_approximable N phi G f ->
  is_vector_lone_approximable N phi G g ->
  is_vector_lone_approximable N phi G (fun x => f x+g x).
Proof.
move=> hf hg hfa hga e he.
have he2 : 0 < e/2 by rewrite divr_gt0 // ltr0n.
have [u [a [hu [hi ha]]]] := hfa _ he2.
have [v [b [hv [hj hb]]]] := hga _ he2.
have [c [hc hcb]] := @vector_norm_error_triangle_integral R X E N hN phi hphi
  f g u v a b hf hg (hGA u hu) (hGA v hv) hi hj.
exists (fun x => u x+v x),c; split; first exact: hG.
split=> //.
have hab := ltrD ha hb; rewrite -splitr in hab; exact: le_lt_trans hcb hab.
Qed.
