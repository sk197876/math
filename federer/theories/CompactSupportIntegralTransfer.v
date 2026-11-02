(** Supporting identification of compact-test integrals in Federer (1969),
    2.5.14, pp. 107–108. Once finite measurable sets retain their measures,
    the characteristic expansion transfers positive integrals; positive and
    negative parts then transfer all of K(X). We use only the project's
    already proved 2.3.3 and 2.4.8 and the signed-parts argument of 2.5.2,
    p. 93. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactSupportMeasureFinite
  NonnegativeIntegralFiniteTransfer FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  RealIntegralFunctionalUP SummableRealFunctionUP SummableRealArithmetic DensityCharacteristicIntegral
  MeasureIntegralGraphEquivalence ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_support_positive_integral_transfer]: the nonnegative
    case of the representation identity in Federer 2.5.14, p. 107 Compact
    finiteness is used for the original measure without assuming the compact
    support is measurable. *)
Lemma compact_support_positive_integral_transfer (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A) :
  hausdorff_space X -> locally_compact (@setT X) ->
  (forall S, measure_measurable mu S -> mu S < +oo -> measure_measurable nu S /\ nu S=mu S) ->
  is_real_integral_functional nu (positive_function_lattice (@compactly_supported_continuous_functions R X)) A.
Proof.
move=> hh hl ht f hf.
pose F x : extended_real_line R := (f x)%:E.
have hp x : 0 <= F x by rewrite /F lee_fin; exact: hf.2.
have hsub : [set x | F x <> 0] `<=` real_function_support f.
  move=> x hx; apply: subset_closure=> hz; apply: hx; by rewrite /F hz.
have hfin : mu [set x | F x <> 0] < +oo.
  exact (le_lt_trans (@measure_mono R X mu hm _ _ hsub)
    (@compact_support_representing_measure_compact_finite R X mu A hm hA hh hl _ hf.1.2)).
have hi : is_measure_integral mu (partial_function_total F) (A f)%:E.
  exact: measure_integral_graph_equivalent (real_total_embedding_graph f) (hA f hf.1).
have hj := @nonnegative_integral_finite_measure_transfer R X mu nu hm hn F (A f)%:E ht hp hfin hi.
apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ hj)=> x y.
exact: iff_sym (real_total_embedding_graph f x y).
Qed.

(** Source for [compact_support_integral_transfer]: all of K(X) satisfies
    the representation identity in Federer 2.5.14, p. 107 Positive and
    negative parts have finite integrals, so the resulting signed difference
    never subtracts two infinities. *)
Theorem compact_support_integral_transfer (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (A : (X -> R) -> R) (hm : is_measure mu) (hn : is_measure nu)
    (hA : is_real_integral_functional mu (@compactly_supported_continuous_functions R X) A)
    (hD : is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A) :
  hausdorff_space X -> locally_compact (@setT X) ->
  (forall S, measure_measurable mu S -> mu S < +oo -> measure_measurable nu S /\ nu S=mu S) ->
  is_real_integral_functional nu (@compactly_supported_continuous_functions R X) A.
Proof.
move=> hh hl ht f hf.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hpos := @compact_support_positive_integral_transfer R X mu nu A hm hn hA hh hl ht.
pose p x := Order.max (f x) 0%R.
pose q x := (p x-f x)%R.
have hpL := function_lattice_positive_part hL hf.
have hp0 : function_nonnegative p by move=> x; rewrite /p le_max lexx orbT.
have hfp : function_le f p by move=> x; rewrite /p le_max lexx.
have hqL := function_lattice_ordered_difference hL hf hpL hfp.
have hq0 : function_nonnegative q by move=> x; rewrite /q subr_ge0; exact: hfp.
have hip := hpos p (conj hpL hp0).
have hiq := hpos q (conj hqL hq0).
have hi := @real_total_integral_subtract R X nu hn p q (A p) (A q) hip hiq.
have hfun : (fun x => (p x-q x)%R)=f.
  by apply: funext=> x; rewrite /q opprB addrCA subrr addr0.
have hadd : (fun x => (f x+q x)%R)=p.
  by apply: funext=> x; rewrite /q addrCA subrr addr0.
have hval := @monotone_daniell_integral_add R X _ A hD f q hf hqL.
rewrite hadd in hval; by rewrite hfun hval addrK in hi.
Qed.
