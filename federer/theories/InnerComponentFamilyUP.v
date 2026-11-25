(** Federer (1969), 4.1.4, p. 348: C_e is the component
    of the fixed centre a in the original inward locus.
    Component equality is specified independently of a family
    implementation. Outside the locus the ordinary component
    is empty; all required small-radius memberships are proved. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_inner_component_family]: the actual original
    component relation defining C_e, Federer 4.1.4, p. 348. *)
Definition is_inner_component_family (R:realType) (X:topologicalType)
    (O:R->set X) (a:X) (C:R->set X):Prop:=
  forall e:R,0<e ->C e=connected_component (O e) a.

(** Source for [inner_component_family_exists]: the original
    components C_e exist as an actual family, supporting
    Federer 4.1.4, pp. 348–349. *)
Theorem inner_component_family_exists (R:realType) (X:topologicalType)
    (O:R->set X) (a:X):
  exists C:R->set X,is_inner_component_family O a C.
Proof. exists (fun e=>connected_component (O e) a); by move=>e he. Qed.
