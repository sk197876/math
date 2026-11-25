(** Federer (1969), 4.1.25, p. 383: the
    source side of the weighted area formula is
    precisely the original paired exterior-image integral.
    Both partial factors retain the full differential
    domain. The equality includes the zero-Jacobian case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ExteriorGrading ExteriorMaps AlternatingForms AlternatingPairing
  EuclideanLinearJacobian Jacobian EuclideanJacobianMeasurable
  PartialFunctionUP PartialFunctionPostcomposition PartialDensityProduct
  CurrentLipschitzLebesgueActionIntegrand CurrentAreaPairingQuotientUP
  CurrentAreaPairingQuotientSealed CurrentAreaPairingQuotientLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_pairing_quotient_product_graph]:
    quotient times the actual Jacobian equals the
    original scalar numerator on exactly the original
    differential domain, supporting 4.1.25, p. 383.
    Undefined differentials receive no scalar values. *)
Theorem current_area_pairing_quotient_product_graph (R:realType)
    (h2:(1+1:R)!=0) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m) x z :
  partial_function_graph
    (partial_density_product (@CurrentAreaPairingQuotient.value R m n f xi a)
      (extended_euclidean_jacobian f)) x z <->
  partial_function_graph
    (@current_lipschitz_lebesgue_action_integrand R m n m f xi (fun _=>a)) x z.
Proof.
have hJGraph y (D:Hom (R_n R m) (R_n R n))
    (hD:has_norm_differential
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f y D) :
    partial_function_graph (extended_euclidean_jacobian f) y
      (@euclidean_linear_jacobian R m n m D)%:E.
  exists (euclidean_linear_jacobian m D);split;last reflexivity.
  apply:(euclidean_jacobian_graph m setT f y _).2.
  by exists D.
rewrite partial_density_product_graph
  current_lipschitz_lebesgue_action_integrand_graph.
split.
- move=>[r [j [hr [hj hValue]]]].
  have [D [hD hR]]:=(@CurrentAreaPairingQuotient.laws R m n f xi a x r).1 hr; subst r.
  have hJ:j=(@euclidean_linear_jacobian R m n m D)%:E:=
    esym (partial_function_single_valued (hJGraph x D hD) hj).
  exists D;split;first exact:hD.
  rewrite hJ -EFinM
    (@current_area_pairing_quotient_times_jacobian R m n xi a h2 x D) in hValue.
  exact:hValue.
- move=>[D [hD hValue]].
  exists (current_area_pairing_quotient_coefficient xi a x D)%:E,
    (@euclidean_linear_jacobian R m n m D)%:E.
  split.
  + exact:(@current_area_pairing_quotient_at_differential R m n f xi a x D hD).
  + split;first exact:hJGraph x D hD.
    by rewrite -EFinM
      (@current_area_pairing_quotient_times_jacobian R m n xi a h2 x D).
Qed.
