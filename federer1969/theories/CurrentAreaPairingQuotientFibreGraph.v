(** Federer (1969), 4.1.25, p. 383: on a
    good original fibre, summing the auxiliary scalar
    quotient gives exactly the scalar pairing of the
    original normalized vector summands. No undefined
    source point is silently replaced in the fibre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations ExteriorGrading
  AlternatingForms AlternatingPairing PartialFunctionUP
  PartialFunctionPostcomposition PartialFibreNumericalSum
  CurrentAreaNormalisedImageSealed CurrentAreaPairingQuotientSealed
  CurrentAreaPairingQuotientLaws CurrentAreaFibreSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_pairing_quotient_fibre_graph]:
    the exact original scalar fibre sum in 4.1.25,
    p. 383, agrees with the area auxiliary whenever
    every original vector summand on the fibre is
    defined. Existence and signed-sum definedness are
    preserved in both directions. *)
Theorem current_area_pairing_quotient_fibre_graph (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (a:A_m (R_n R n) R^o m) y z :
  (forall x,f x=y->partial_function_domain
    (@CurrentAreaNormalisedImage.value R m n f xi) x) ->
  (partial_function_graph
    (partial_fibre_numerical_sum f (@CurrentAreaPairingQuotient.value R m n f xi a)) y z <->
   partial_function_graph
    (partial_fibre_numerical_sum f
      (@current_area_fibre_pairing_integrand R (R_n R m) n m
        (@CurrentAreaNormalisedImage.value R m n f xi) a)) y z).
Proof.
move=>hDomain.
have hPoint x (hx:f x=y) v:
    partial_function_graph (@CurrentAreaPairingQuotient.value R m n f xi a) x v <->
    partial_function_graph (@current_area_fibre_pairing_integrand R (R_n R m) n m
      (@CurrentAreaNormalisedImage.value R m n f xi) a) x v.
  split.
  - move=>hQ.
    have [w hW]:=@hDomain x hx.
    have hKnown:=@current_area_pairing_quotient_normalised_value R m n f xi a x w hW.
    exists w;split;first exact:hW.
    exact:partial_function_single_valued hKnown hQ.
  - move=>[w [hW hValue]].
    rewrite -hValue.
    exact:(@current_area_pairing_quotient_normalised_value R m n f xi a x w hW).
rewrite !partial_fibre_numerical_sum_graph.
split.
- move=>[w [hW hSum]];exists w;split;last exact:hSum.
  move=>x hx;exact:(@hPoint x hx (w x)).1 (@hW x hx).
- move=>[w [hW hSum]];exists w;split;last exact:hSum.
  move=>x hx;exact:(@hPoint x hx (w x)).2 (@hW x hx).
Qed.
