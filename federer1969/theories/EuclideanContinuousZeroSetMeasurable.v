(** Federer (1969), 3.1.24, p. 240: the zero
    set of a continuous map on an open Euclidean domain is
    measurable, permitting the use of 2.9.11 in the root-set proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerNormTopologyAdapters RealNormUP NormClassOneUP NormClassZeroTopology
  NormClassZeroNonzeroLocus EuclideanLebesgueDimensions MeasureUP MeasureFiniteClosure
  TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_continuous_zero_set_measurable]: supporting
    the use of 2.9.11 in Federer 3.1.24, p. 240.
    The zero set is the open domain minus its open nonzero
    locus, hence is Borel and Lebesgue measurable. The normed
    target is arbitrary and need not be finite dimensional. *)
Theorem euclidean_continuous_zero_set_measurable (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R n)) (f:R_n R n->Y) :
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY A f ->
  measure_measurable (@euclidean_lebesgue_measure R n) (fun x=>A x /\ f x=0).
Proof.
move=>hf.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose U:=fun x=>A x /\ f x!=0.
have hA:= (inner_norm_openP (@euclidean_inner_productP R n) A).2
  (@norm_class_zero_domain_open R (R_n R n) Y _ NY hNX A f hf).
have hU: @open (inner_metric_space (@euclidean_inner_productP R n)) U.
  exact ((inner_norm_openP (@euclidean_inner_productP R n) U).2
    (@norm_class_zero_nonzero_locus_open R (R_n R n) Y _ NY hNX hNY A f hf)).
have hm:=euclidean_lebesgue_is_measure R n.
have hr:=euclidean_lebesgue_borel_regular R n.
have hAm:=borel_regular_open_measurable hr hA.
have hUm:=borel_regular_open_measurable hr hU.
have he:(fun x=>A x /\ f x=0)= A `\` U.
  apply/seteqP; split=>x hx.
  - split; first exact hx.1.
    move=>[_ hn]; by rewrite hx.2 eqxx in hn.
  - split; first exact hx.1.
    case:(pselect (f x=0))=>[h|h]; first exact h.
    exfalso; apply:hx.2; split; first exact hx.1.
    by apply/eqP.
rewrite he; exact (measure_measurable_difference hm hAm hUm).
Qed.
