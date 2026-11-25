(** Federer (1969), 4.1.5, p. 349: the original
    finite-gauge hypothesis applies to a compact cutoff
    equal to one on a prescribed common support. The
    existing localized cutoff supplies this majorant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff DistributionVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_finite_gauge_cutoff]: the choice
    of a compact positive majorant g and its finite
    original gauge in the extension argument of Federer
    4.1.5, p. 349. *)
Theorem distribution_finite_gauge_cutoff (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o):
  hausdorff_space X ->locally_compact (@setT X) ->open U ->
  (forall f:X->R,
    @positive_function_lattice R X (@compactly_supported_continuous_functions R X) f ->
    @real_function_support R X f `<=` U ->
    exists b:R,is_distribution_variation_value NY value S f b%:E) ->
  forall C:set X,compact C ->C `<=` U ->
  exists g:X->R,exists b:R,is_localized_compact_cutoff C U g /\
    is_distribution_variation_value NY value S g b%:E.
Proof.
move=>hh hl hU hFinite C hC hCU.
pose g:=@localized_compact_cutoff R X C U hh hl hC hU hCU.
have hG:=@localized_compact_cutoff_specification R X C U hh hl hC hU hCU.
have hPositive:@positive_function_lattice R X (@compactly_supported_continuous_functions R X) g.
  split; first exact:compact_cutoff_function (localized_compact_cutoff_laws hG).
  move=>x; exact:(andP (compact_cutoff_range (localized_compact_cutoff_laws hG) x)).1.
have[b hGauge]:=hFinite g hPositive (localized_compact_cutoff_support hG).
by exists g,b.
Qed.
