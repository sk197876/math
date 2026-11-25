(** Federer (1969), 4.1.5, p. 350:
    S(b_(x,r)y) is exactly the subset integral
    of the original scalar evaluation. The graph
    identity uses only the independently specified
    characteristic function and dual linearity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  CharacteristicFunctionUP SummableRealFunctionUP AbstractDualPartialPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [abstract_dual_characteristic_pairing_graph]:
    the exact characteristic pairing in the
    ball quotient of Federer 4.1.5, p. 350. *)
Lemma abstract_dual_characteristic_pairing_graph (R:realType) (X:choiceType)
    (Y D:lmodType R) (ed:Hom D (Hom Y R^o)) (xi:X->D)
    (A:set X) (s:X->R) (hs:is_characteristic_function A s) (y:Y) x z:
  partial_function_graph (abstract_dual_partial_pairing ed xi
    (partial_function_total (fun x=>s x*:y))) x z <->
  partial_function_graph (partial_function_zero_extension 0 A
    (real_total_integrand (fun x=>ed (xi x) y))) x z.
Proof.
rewrite abstract_dual_partial_pairing_total_graph real_total_integrand_graph
  partial_function_zero_extension_graph.
case:(pselect (A x))=>hx.
- rewrite (characteristic_on_set hs hx) scale1r.
  split=>hz; first by left; split=>//; apply/real_total_integrand_graph.
  case:hz=>[[_ hZ]|[hNot _]]; last exact:(False_ind _ (hNot hx)).
  exact:(real_total_integrand_graph _ _ _).1 hZ.
- rewrite (characteristic_off_set hs hx) scale0r linear0.
  split=>hz; first by right; split=>//; symmetry.
  case:hz=>[[hA _]|[_ hZ]]; first exact:(False_ind _ (hx hA)).
  by rewrite hZ.
Qed.
