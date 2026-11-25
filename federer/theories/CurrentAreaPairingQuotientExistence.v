(** Federer (1969), 4.1.25, p. 383: existence
    of the auxiliary scalar quotient on the full
    original differential domain. The independently stated
    graph, not this construction, is its public interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferential
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading AlternatingForms PartialFunctionUP
  PartialFunctionSourcePostcomposition CurrentAreaPairingQuotientUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_pairing_quotient_exists]:
    the scalar auxiliary in the weighted-area argument
    of 4.1.25, p. 383, exists on every actual
    differential point. Nondifferentiable points get no value. *)
Theorem current_area_pairing_quotient_exists (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m) :
  exists q:partial_function (R_n R m) (extended_real_line R),
    is_current_area_pairing_quotient f xi a q.
Proof.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose DF:=norm_differential hNX hNY setT f.
pose q:=partial_function_source_postcompose DF
  (fun x D=>(current_area_pairing_quotient_coefficient xi a x D)%:E).
exists q=>x z.
rewrite /q partial_function_source_postcompose_graph.
split.
- move=>[D [hD hValue]];exists D;split;last exact:hValue.
  exact:(norm_differential_graph hNX hNY setT f x D).1 hD.
- move=>[D [hD hValue]];exists D;split;last exact:hValue.
  exact:(norm_differential_graph hNX hNY setT f x D).2 hD.
Qed.
