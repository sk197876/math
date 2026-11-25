(** Federer (1969), 4.1.25, p. 383: on a
    full original fibre f(x)=y, the actual test
    takes the fixed covector value psi(y). Thus its
    source-dependent scalar sum is exactly the pairing
    of the original vector fibre sum with psi(y). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations ExteriorGrading
  AlternatingForms AlternatingPairing PartialFunctionUP
  PartialFunctionPostcomposition PartialFunctionSourcePostcomposition
  PartialFibreNumericalSum CurrentAreaNormalisedImageSealed
  CurrentAreaPairingQuotientSealed CurrentAreaPairingQuotientTestSealed
  CurrentAreaPairingQuotientTestLaws CurrentAreaPairingQuotientFibreGraph
  CurrentAreaFibreSumUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_area_pairing_quotient_test_original_integrand]:
    pair each original normalized vector summand with
    psi(f(x)) in the second display of 4.1.25,
    p. 383. Its partial domain is the original
    normalized vector domain, including for zero tests. *)
Definition current_area_pairing_quotient_test_original_integrand (R:realType) m n
    (f:R_n R m->R_n R n)
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m):
    partial_function (R_n R m) (extended_real_line R):=
  partial_function_source_postcompose
    (@CurrentAreaNormalisedImage.value R m n f xi)
    (fun x v=>(pairing v (phi (f x)))%:E).

Section TargetTestFibre.
Variable R:realType.
Variables m n:nat.
Local Notation X:=(R_n R m).
Local Notation Y:=(R_n R n).
Variables (f:X->Y) (xi:X->exterior_power X m) (phi:Y->A_m Y R^o m).
Local Notation u:=(@CurrentAreaNormalisedImage.value R m n f xi).
Local Notation original:=(@current_area_pairing_quotient_test_original_integrand
  R m n f xi phi).

(** Source for [current_area_pairing_quotient_test_original_fixed_fibre_graph]:
    the test covector is constant on the literal
    fibre in 4.1.25, p. 383. This exact
    graph equality does not discard undefined summands. *)
Lemma current_area_pairing_quotient_test_original_fixed_fibre_graph y z:
  partial_function_graph (partial_fibre_numerical_sum f original) y z <->
  partial_function_graph (partial_fibre_numerical_sum f
    (@current_area_fibre_pairing_integrand R X n m u (phi y))) y z.
Proof.
have hPoint x (hx:f x=y) v:
    partial_function_graph original x v <->
    partial_function_graph
      (@current_area_fibre_pairing_integrand R X n m u (phi y)) x v.
  rewrite /current_area_pairing_quotient_test_original_integrand
    partial_function_source_postcompose_graph
    /current_area_fibre_pairing_integrand /partial_function_postcompose hx.
  reflexivity.
rewrite !partial_fibre_numerical_sum_graph.
split.
- move=>[w [hW hSum]];exists w;split;last exact:hSum.
  move=>x hx;exact:(@hPoint x hx (w x)).1 (@hW x hx).
- move=>[w [hW hSum]];exists w;split;last exact:hSum.
  move=>x hx;exact:(@hPoint x hx (w x)).2 (@hW x hx).
Qed.

(** Source for [current_area_pairing_quotient_test_fibre_graph]:
    the variable-test scalar auxiliary has the
    exact original normalized fibre sum on every
    good fibre of 4.1.25, p. 383. *)
Theorem current_area_pairing_quotient_test_fibre_graph y z:
  (forall x,f x=y->partial_function_domain u x) ->
  (partial_function_graph (partial_fibre_numerical_sum f
    (@CurrentAreaPairingQuotientTest.value R m n f xi phi)) y z <->
   partial_function_graph (partial_fibre_numerical_sum f original) y z).
Proof.
move=>hDomain.
have hFixed:
    partial_function_graph (partial_fibre_numerical_sum f
      (@CurrentAreaPairingQuotientTest.value R m n f xi phi)) y z <->
    partial_function_graph (partial_fibre_numerical_sum f
      (@CurrentAreaPairingQuotient.value R m n f xi (phi y))) y z.
  have hPoint x (hx:f x=y) v:
      partial_function_graph (@CurrentAreaPairingQuotientTest.value R m n f xi phi) x v <->
      partial_function_graph (@CurrentAreaPairingQuotient.value R m n f xi (phi y)) x v.
    by rewrite current_area_pairing_quotient_test_fixed_graph hx.
  rewrite !partial_fibre_numerical_sum_graph.
  split.
  - move=>[w [hW hSum]];exists w;split;last exact:hSum.
    move=>x hx;exact:(@hPoint x hx (w x)).1 (@hW x hx).
  - move=>[w [hW hSum]];exists w;split;last exact:hSum.
    move=>x hx;exact:(@hPoint x hx (w x)).2 (@hW x hx).
rewrite hFixed
  (@current_area_pairing_quotient_fibre_graph R m n f xi (phi y) y z hDomain).
symmetry;exact:current_area_pairing_quotient_test_original_fixed_fibre_graph.
Qed.

(** Source for [current_area_pairing_quotient_test_original_fibre_value]:
    the original universal covector sum law, applied
    to the actual test value psi(y), identifies the
    fibre scalar in 4.1.25, p. 383. *)
Theorem current_area_pairing_quotient_test_original_fibre_value y eta:
  @is_current_area_fibre_sum R X n m f u y eta ->
  partial_function_graph (partial_fibre_numerical_sum f original) y
    (pairing eta (phi y))%:E.
Proof.
move=>hEta.
apply:(@current_area_pairing_quotient_test_original_fixed_fibre_graph y _).2.
exact:hEta (phi y).
Qed.
End TargetTestFibre.
