(** Federer (1969), 2.2.15, p. 70: private existence of the smallest Baire
    class containing continuous functions. The intersection of all candidate
    classes has the required closure, containment and minimality properties.
    This is a local construction, not an invocation of an external Baire
    hierarchy. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import PointwiseLimit BaireFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [baire_function_family_exists]: supporting
    existence of the smallest class used to define Baire functions
    in Federer 2.2.15, p. 70. Membership means
    membership in every class satisfying the defining closure and
    continuous-generator conditions. *)
Theorem baire_function_family_exists (R : realType) (X : topologicalType) (Y : metricType R) :
  exists F : set (X -> Y), is_baire_function_family F.
Proof.
pose F := [set f : X -> Y | forall G : set (X -> Y),
  is_baire_class G -> (forall h, continuous h -> G h) -> G f].
exists F; constructor.
- move=> f g hf hlim G hG hc.
  have hfn n : G (f n) := hf n G hG hc.
  exact: hG f g hfn hlim.
- move=> f hf G hG hc; exact: hc f hf.
- move=> G hG hc f hf; exact: hf G hG hc.
Qed.
