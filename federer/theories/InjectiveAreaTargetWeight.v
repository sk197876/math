(** Federer (1969), 3.2.10, p. 248: on a univalent
    coordinate piece, the multiplicity factor in 3.2.5 is
    precisely the characteristic function of the image. Retain
    the zero-times-infinity convention and exact integral graphs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension AreaTransformIntegrands MappingMultiplicity MappingMultiplicityLaws
  MappingPartitionMultiplicity CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [injective_area_target_weight_graph]: the
    integral over u(B) in Federer 3.2.10, p. 248,
    obtained from 3.2.5, pp. 244–245. This is a
    supporting exact graph identity for every finite real weight,
    before any measurability or integrability is assumed. *)
Lemma injective_area_target_weight_graph (R:realType) m n
    (u:R_n R m->R_n R n) (B:set (R_n R m)) (g:R_n R n->R):
  {in B &,injective u} ->forall y z,
  partial_function_graph (area_transform_target_integrand u B g) y z <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
    (u @` B) (partial_function_total (fun w=>(g w)%:E:extended_real_line R))) y z.
Proof.
move=>hInj y z.
pose s:=@CharacteristicFunction.value R (R_n R n) (u @` B).
have hs:=@CharacteristicFunction.laws R (R_n R n) (u @` B).
have hN:=injective_mapping_multiplicity_characteristic hInj hs.
case:(pselect ((u @` B) y))=>hy.
- rewrite (@partial_function_zero_extension_on _ _ (0:extended_real_line R) (u @` B)
    (partial_function_total (fun w=>(g w)%:E:extended_real_line R)) y z hy).
  change ((g y)%:E*@mapping_multiplicity R _ _ u B y=z <->(g y)%:E=z).
  by rewrite hN (characteristic_on_set hs hy) mule1.
- rewrite (@partial_function_zero_extension_off _ _ (0:extended_real_line R) (u @` B)
    (partial_function_total (fun w=>(g w)%:E:extended_real_line R)) y z hy).
  change ((g y)%:E*@mapping_multiplicity R _ _ u B y=z <->z=0).
  rewrite hN (characteristic_off_set hs hy) mule0.
  split=>he; exact (Logic.eq_sym he).
Qed.
