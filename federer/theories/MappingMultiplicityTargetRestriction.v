(** Federer (1969), 3.2.6, p. 245: restricting
    the target integration set amounts to restricting source
    fibres to its inverse image. This supporting counting
    identity retains infinite multiplicities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MappingMultiplicity MappingMultiplicityLaws CountingMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [multiplicity_target_restriction_graph]:
    supporting characteristic-weight identity for Federer
    3.2.6, p. 245. The target set need not
    be measurable for this exact fibre comparison. *)
Lemma multiplicity_target_restriction_graph (R:realType) (X Y:choiceType)
    (f:X->Y) (A:set X) (T:set Y) y z:
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) T
    (partial_function_total (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R)))) y z <->
  partial_function_graph (partial_function_total (fun y=>
    (@mapping_multiplicity R X Y f (A `&` (f @^-1` T)) y:extended_real_line R))) y z.
Proof.
case:(pselect (T y))=>hy.
- rewrite (partial_function_zero_extension_on _ _ _ hy).
  have he:[set x|A x /\ f x=y]=[set x|(A x /\ T (f x)) /\ f x=y].
    apply/seteqP; split=>x.
    + move=>[hx hxy]; split=>//; split=>//; by rewrite hxy.
    + by move=>[[hx _] hxy].
  change (@mapping_multiplicity R X Y f A y=z <->
    @mapping_multiplicity R X Y f (A `&` (f @^-1` T)) y=z).
  by rewrite /mapping_multiplicity /mapping_fibre he.
- rewrite (partial_function_zero_extension_off _ _ _ hy).
  have hZero:@mapping_multiplicity R X Y f (A `&` (f @^-1` T)) y=0.
    apply:(@mapping_multiplicity_zero_iff R X Y f (A `&` (f @^-1` T)) y).2.
    move=>[x [hx hTx] hxy]; apply:hy; by rewrite -hxy.
  change (z=0 <-> @mapping_multiplicity R X Y f (A `&` (f @^-1` T)) y=z).
  by rewrite hZero; split=>->.
Qed.
