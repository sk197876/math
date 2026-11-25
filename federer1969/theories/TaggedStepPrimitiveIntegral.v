(** Federer (1969), 2.9.24, p. 169: integrating each tagged step cell
    against g' gives its tag value times the increment of g, by 2.9.20(1),
    p. 165. This file proves that finite identity for any supplied total
    density with the actual primitive cell integrals. A later application
    uses a proof representative of g'. The local Federer erratum has no
    entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral MeasureConullZeroIntegral
  SummableRealFunctionUP SummableRealArithmetic LebesgueScalarMeasure
  LebesgueRightClosedIntegral TotalScalarCutoff StieltjesSums TaggedStepFunction TaggedStepProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [tagged_step_primitive_integral]: supporting exact finite
    integral identity before telescoping in Federer 2.9.24, p. 169 Cell
    primitives give the actual integral, including negative or zero tag
    values and zero-width cells. The density need not be globally summable:
    each approximation has bounded interval support. *)
Theorem tagged_step_primitive_integral (R : realType) (g v : R -> R)
    (a b : R) :
  (forall u z : R, a<=u -> u<=z -> z<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,z]
      (real_total_integrand v) (g z-g u)%:E) ->
  forall (f : R -> R) (w : seq R), sorted <=%O w ->
    (forall t : R, t \in w -> a<=t<=b) ->
    is_measure_integral (@lebesgue_scalar_measure R)
      (real_total_integrand (fun x => tagged_step_function f w x*v x))
      (stieltjes_sum f g w)%:E.
Proof.
move=> hprimitive f w.
have hm := lebesgue_scalar_is_measure R.
have hzero (s : seq R) : (size s<=2)%N ->
    is_measure_integral (@lebesgue_scalar_measure R)
      (real_total_integrand (fun x => tagged_step_function f s x*v x)) 0.
  move=> hs; apply: (measure_almost_zero_integral hm).
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) _ hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  apply/real_total_integrand_graph.
  by rewrite (@tagged_step_function_short R f s hs x) mul0r.
have [n] := ubnP (size w).
elim: n w=> [//|n ih] [|u [|r [|z rest]]] hsize hs htags;
  try by apply: hzero; rewrite /=.
have /andP[hur /andP[hrz htail]] := hs.
have huz : u<=z := le_trans hur hrz.
have /andP[hau _] := htags u (mem_head u (r::z::rest)).
have hzmem : z \in u::r::z::rest by rewrite !in_cons eqxx !orbT.
have /andP[_ hzb] := htags z hzmem.
have hcell := hprimitive u z hau huz hzb.
have hcut := lebesgue_right_closed_cutoff_integral hcell.
have hscaled := @real_total_integral_scale R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm _ _ (f r) hcut.
have hsmall : (size (z::rest)<n)%N by move: hsize; rewrite /= !ltnS; exact: ltnW.
have hrest := ih (z::rest) hsmall htail.
have htailtags (t : R) : t \in z::rest -> a<=t<=b.
  move=> ht; apply: htags.
  rewrite in_cons; apply/orP; right; rewrite in_cons; apply/orP; right; exact: ht.
have hI := hrest htailtags.
have hsum := @real_total_integral_add R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm _ _ _ _ hscaled hI.
rewrite (@tagged_step_first_cell_product R f v u r z rest hs).
exact: hsum.
Qed.
