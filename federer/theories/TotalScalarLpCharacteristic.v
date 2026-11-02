(** Federer (1969), 2.5.7, pp. 98–99: localization by the characteristic
    function of a measurable set, both for closure of the candidate
    densities under maximum and for the maximality contradiction. We use the
    abstract characteristic laws and retain the full Lp membership
    conditions at infinity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP CharacteristicFunctionUP MeasurableFunctionUP
  MeasurableTotalPiecewise MeasurableTotalBasic TotalScalarLpUP TotalScalarLpClosure TotalScalarLpLattice FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_characteristic_piece]: the assertion f*s
    belongs to L in Federer 2.5.7, pp. 98–99 The characteristic function
    itself need not be summable. *)
Lemma total_scalar_lp_characteristic_piece (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p
    (E : set X) (s f : X -> R) :
  is_characteristic_function E s -> measure_measurable mu E -> total_scalar_lp mu p f ->
  total_scalar_lp mu p (fun x => (f x*s x)%R).
Proof.
move=> hs hE hf; apply: (@total_scalar_lp_domination R X mu hm p f _ hf).
- have he : (fun x => (f x*s x)%R)=(fun x => if pselect (E x) then f x else 0%R).
    apply: funext=> x; case: (pselect (E x))=> hx.
    + by rewrite (characteristic_on_set hs hx) mulr1.
    + by rewrite (characteristic_off_set hs hx) mulr0.
  rewrite he; apply: (@measurable_total_piecewise R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm E f (fun _ => 0%R) hE hf.2.1).
  exact: (@measurable_total_constant R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R).
- move=> x; case: (pselect (E x))=> hx.
  + by rewrite (characteristic_on_set hs hx) mulr1.
  + by rewrite (characteristic_off_set hs hx) mulr0 normr0 normr_ge0.
Qed.

(** Source for [positive_lp_characteristic_pieces]: both positive pieces f*s
    and f-f*s in Federer 2.5.7, pp. 98–99 No finite measure of E or of its
    complement is required. *)
Lemma positive_lp_characteristic_pieces (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p
    (E : set X) (s f : X -> R) :
  is_characteristic_function E s -> measure_measurable mu E ->
  positive_function_lattice (total_scalar_lp mu p) f ->
  positive_function_lattice (total_scalar_lp mu p) (fun x => (f x*s x)%R) /\
  positive_function_lattice (total_scalar_lp mu p) (fun x => (f x-f x*s x)%R).
Proof.
move=> hs hE hf.
have hfs := @total_scalar_lp_characteristic_piece R X mu hm p E s f hs hE hf.1.
have hrest := @total_scalar_lp_subtract R X mu hm p f _ hf.1 hfs.
split; split=> // x; case: (pselect (E x))=> hx.
- by rewrite (characteristic_on_set hs hx) mulr1; exact: hf.2.
- by rewrite (characteristic_off_set hs hx) mulr0.
- by rewrite (characteristic_on_set hs hx) mulr1 subrr.
- by rewrite (characteristic_off_set hs hx) mulr0 subr0; exact: hf.2.
Qed.
