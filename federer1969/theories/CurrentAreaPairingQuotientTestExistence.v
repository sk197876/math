(** Federer (1969), 4.1.25, p. 383: existence
    of the scalar area auxiliary for a variable target
    form. Reuse the actual differential graph; no value
    is assigned at an undefined differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferential
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading AlternatingForms PartialFunctionUP
  PartialFunctionSourcePostcomposition CurrentAreaPairingQuotientUP
  CurrentAreaPairingQuotientTestUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_pairing_quotient_test_exists]:
    the variable-form scalar auxiliary in 4.1.25,
    p. 383, exists for every map and every field;
    analytic hypotheses enter its integral laws later. *)
Theorem current_area_pairing_quotient_test_exists (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m) :
  exists q:partial_function (R_n R m) (extended_real_line R),
    is_current_area_pairing_quotient_test f xi phi q.
Proof.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose DF:=norm_differential hNX hNY setT f.
pose q:=partial_function_source_postcompose DF
  (fun x D=>(current_area_pairing_quotient_coefficient xi (phi (f x)) x D)%:E).
exists q=>x z.
rewrite /q partial_function_source_postcompose_graph.
split.
- move=>[D [hD hValue]];exists D;split;last exact:hValue.
  exact:(norm_differential_graph hNX hNY setT f x D).1 hD.
- move=>[D [hD hValue]];exists D;split;last exact:hValue.
  exact:(norm_differential_graph hNX hNY setT f x D).2 hD.
Qed.
