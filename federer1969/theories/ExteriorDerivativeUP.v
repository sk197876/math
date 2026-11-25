(** Federer (1969), 4.1.6, p. 352: exterior
    differentiation uses the actual first differential
    on its original domain. The partial graph is
    specified independently; no derivative value is
    assigned at a point of nondifferentiability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  AlternatingForms PartialFunctionUP ExteriorDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [has_exterior_derivative]: d phi(a) is
    obtained from the actual D phi(a) by the original
    signed tuple formula, Federer 4.1.6, p. 352. *)
Definition has_exterior_derivative (R:realType) (V W:lmodType R)
    (NV:V->R) m (NP:A_m V W m->R) (U:V->Prop)
    (phi:V->A_m V W m) (a:V) (b:A_m V W m.+1):Prop:=
  exists L:Hom V (A_m V W m),has_norm_differential NV NP U phi a L /\
    is_exterior_differential_value L b.

(** Source for [is_exterior_derivative_graph]: the
    original derivative is defined exactly where its
    first differential exists, through the characteristic
    formula, Federer 4.1.6, p. 352. Existence
    of the alternating value is proved separately. *)
Definition is_exterior_derivative_graph (R:realType) (V W:lmodType R)
    (NV:V->R) m (NP:A_m V W m->R) (U:V->Prop)
    (phi:V->A_m V W m) (D:partial_function V (A_m V W m.+1)):Prop:=
  forall a b,partial_function_graph D a b <->has_exterior_derivative NV NP U phi a b.

(** Source for [exterior_derivative_unique]: the
    original exterior derivative value is unique,
    Federer 4.1.6, p. 352, by uniqueness of
    the actual first differential and form evaluation. *)
Lemma exterior_derivative_unique (R:realType) (V W:lmodType R)
    (NV:V->R) (hNV:is_real_norm NV) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
    (U:V->Prop) (phi:V->A_m V W m) a b c:
  has_exterior_derivative NV NP U phi a b ->has_exterior_derivative NV NP U phi a c ->b=c.
Proof.
move=>[L [hL hB]] [M [hM hC]].
have hEqual:=norm_differential_unique hNV hNP hL hM.
subst M; exact:exterior_differential_value_unique hB hC.
Qed.
