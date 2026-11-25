(** Federer (1969), 4.1.6, p. 354: divergence
    of a field has the exact original differential
    domain. Its graph uses the independently specified
    linear tensor composite and the sealed actual
    first differential, without values elsewhere. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialSealed
  PartialFunctionUP PartialFunctionPostcomposition
  GrassmannAbbreviations ExteriorGrading DivergenceUP DivergenceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [has_field_divergence]: apply the
    original interior derivative to D xi(x),
    Federer 4.1.6, p. 354. *)
Definition has_field_divergence (R:realType) (h2:(1+1:R)!=0) n p
    (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R)
    (U:R_n R n->Prop) (xi:R_n R n->exterior_power (R_n R n) p.+1) a b:Prop:=
  exists L,has_norm_differential NV NP U xi a L /\is_divergence_value h2 L b.

(** Source for [field_divergence_graph_exists]: the
    original partial divergence is a function,
    Federer 4.1.6, p. 354. Existence
    uses only the already proved sealed differentials
    and linear divergence map. *)
Theorem field_divergence_graph_exists (R:realType) (h2:(1+1:R)!=0) n p
    (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R)
    (hNV:is_real_norm NV) (hNP:is_real_norm NP)
    (U:R_n R n->Prop) (xi:R_n R n->exterior_power (R_n R n) p.+1):
  exists D:partial_function (R_n R n) (exterior_power (R_n R n) p),
    forall a b,partial_function_graph D a b<->has_field_divergence h2 NV NP U xi a b.
Proof.
exists (partial_function_postcompose
  (@NormDifferential.value R (R_n R n) (exterior_power (R_n R n) p.+1) NV NP hNV hNP U xi)
  (@Divergence.value R h2 n p))=>a b; split.
- move=>[L [hL hValue]]; exists L; split.
  + exact:(@NormDifferential.laws R (R_n R n) (exterior_power (R_n R n) p.+1)
      NV NP hNV hNP U xi a L).1 hL.
  + rewrite -hValue; exact:Divergence.laws.
- move=>[L [hL hValue]]; exists L; split.
  + exact:(@NormDifferential.laws R (R_n R n) (exterior_power (R_n R n) p.+1)
      NV NP hNV hNP U xi a L).2 hL.
  + exact:esym (eq_trans hValue (esym (@Divergence.laws R h2 n p L))).
Qed.

Module Type FieldDivergenceSignature.
(** Source for [value]: the original div xi,
    Federer 4.1.6, p. 354. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n p
  (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R),
  is_real_norm NV->is_real_norm NP->(R_n R n->Prop)->
  (R_n R n->exterior_power (R_n R n) p.+1)->
  partial_function (R_n R n) (exterior_power (R_n R n) p).
(** Source for [laws]: the exact original divergence
    graph, Federer 4.1.6, p. 354. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n p
  (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R)
  (hNV:is_real_norm NV) (hNP:is_real_norm NP)
  (U:R_n R n->Prop) (xi:R_n R n->exterior_power (R_n R n) p.+1) a b,
  partial_function_graph (@value R h2 n p NV NP hNV hNP U xi) a b<->
    has_field_divergence h2 NV NP U xi a b.
End FieldDivergenceSignature.
Module FieldDivergence:FieldDivergenceSignature.
(** Source for [value]: select the already proved
    exact graph, Federer 4.1.6, p. 354. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n p
    (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R)
    (hNV:is_real_norm NV) (hNP:is_real_norm NP)
    (U:R_n R n->Prop) (xi:R_n R n->exterior_power (R_n R n) p.+1):=
  projT1 (cid (@field_divergence_graph_exists R h2 n p NV NP hNV hNP U xi)).
(** Source for [laws]: the selected graph retains
    exactly the original values,
    Federer 4.1.6, p. 354. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n p
    (NV:R_n R n->R) (NP:exterior_power (R_n R n) p.+1->R)
    (hNV:is_real_norm NV) (hNP:is_real_norm NP)
    (U:R_n R n->Prop) (xi:R_n R n->exterior_power (R_n R n) p.+1) a b:
  partial_function_graph (@value R h2 n p NV NP hNV hNP U xi) a b<->
    has_field_divergence h2 NV NP U xi a b.
Proof. exact:(projT2 (cid (@field_divergence_graph_exists R h2 n p NV NP hNV hNP U xi)) a b). Qed.
End FieldDivergence.
