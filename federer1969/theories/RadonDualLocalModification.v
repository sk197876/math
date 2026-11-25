(** Federer (1969), 2.5.14, p. 108: local almost uniqueness and changes of
    the representing dual density. A member of Q has compactly supported
    norm, so local equality of densities gives ordinary almost equality of
    their scalar pairings. This supporting lemma distinguishes local
    exceptional sets from globally null sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  VectorDaniellHypotheses VectorDaniellDualExtension VectorDaniellRepresentationUP
  MeasureUP RadonMeasureUP MeasureAlmostUP MeasureAlmostBasic SummableRealFunctionUP
  MeasureIntegralAlmostEquality LocallyNullMeasureUP LocallyNullMeasureModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_dual_locally_equal_pairing]: compact
    support converts local equality into equality of pairings
    almost everywhere, supporting the modification in Federer
    2.5.14, p. 108, of the formula in 2.5.12, p. 103. *)
Lemma radon_dual_locally_equal_pairing (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (k l : X -> weak_dual_space hN) (w : X -> E) :
  measure_locally_almost_everywhere mu [set x | k x=l x] ->
  compactly_supported_continuous_functions (fun x => N (w x)) ->
  measure_almost_equal mu (real_total_integrand (fun x => val (k x) (w x)))
    (real_total_integrand (fun x => val (l x) (w x))).
Proof.
move=> he hw.
pose S := real_function_support (fun x => N (w x)).
pose B := S `&` ~` [set x | k x=l x].
have hB : mu B=0%E := he S (radon_compact_finite hr hw.2).
have ha : measure_almost_everywhere mu (~` B).
  by rewrite /measure_almost_everywhere setCK.
apply: (measure_almost_everywhere_mono hm _ ha)=> x hx.
exists (val (k x) (w x))%:E; split; first by apply/real_total_integrand_graph.
apply/real_total_integrand_graph.
case: (pselect (S x))=> hs.
- have heq : k x=l x by apply: contrapT=> hn; apply: hx; split.
  by rewrite heq.
- have hz : w x=0 := hN.2 _ (real_function_zero_off_support hs).
  by rewrite hz (dual_space_zero (set_valP (k x))) (dual_space_zero (set_valP (l x))).
Qed.

(** Source for [radon_dual_locally_equal_representation]: the
    vector representation of Federer 2.5.14, p. 108,
    is preserved by locally almost equal representatives.
    Measurability is checked by finite Caratheodory tests and
    the integral formula by compact support. *)
Lemma radon_dual_locally_equal_representation (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (k l : X -> weak_dual_space hN) :
  measure_locally_almost_everywhere mu [set x | k x=l x] ->
  is_vector_daniell_density mu Q T k -> is_vector_daniell_density mu Q T l.
Proof.
move=> he hk; constructor.
- apply: (@measurable_total_locally_null_modification R X [the topologicalType of weak_dual_space hN]
    mu hm k l (~` [set x | k x=l x]) he _ (vector_daniell_density_measurable hk)).
  by move=> x hx; apply: contrapT=> hn; exact: hx hn.
- move=> w hw; apply: (measure_integral_almost_equal hm (vector_daniell_density_integral hk hw)).
  apply: (@radon_dual_locally_equal_pairing R X E N hN mu hm hr k l w he).
  exact (@vector_lattice_module_norm R X E N hN
    (@compactly_supported_continuous_functions R X) Q hM w hw).
Qed.
