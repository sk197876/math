(** Federer (1969), 4.1.8, p. 361: the original
    actual-domain join and split remain opaque. Their
    independently specified Euclidean block values are public;
    the subtype construction serves only proved existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanCartesianMap CurrentDomain CurrentCartesianDomainMapsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CartesianCurrentDomainSignature.
(** Source for [join]: the original coordinate identification
    from the pair of actual factor domains, supporting
    Federer 4.1.8, p. 361, by 2.6.5, p. 120. *)
Parameter join:forall (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n)),
  (current_domain R m A*current_domain R n B)%type->
    current_domain R (m+n) (@euclidean_cartesian_set R m n A B).
(** Source for [split]: the inverse original factor-domain
    identification, supporting Federer 4.1.8, p. 361. *)
Parameter split:forall (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n)),
  current_domain R (m+n) (@euclidean_cartesian_set R m n A B)->
    (current_domain R m A*current_domain R n B)%type.
(** Source for [laws]: the opaque maps have exactly
    the original Euclidean block values, supporting Federer
    4.1.8, p. 361, with both zero-dimensional blocks retained. *)
Parameter laws:forall (R:realType) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n)),
  @is_current_cartesian_domain_maps R m n A B
    (@join R m n A B) (@split R m n A B).
End CartesianCurrentDomainSignature.
Module CartesianCurrentDomain:CartesianCurrentDomainSignature.
(** Source for [join]: seal the first map of the
    proved original coordinate witness, supporting Federer
    4.1.8, p. 361. *)
Definition join (R:realType) (m n:nat) (A:set (R_n R m)) (B:set (R_n R n)):
    (current_domain R m A*current_domain R n B)%type->
    current_domain R (m+n) (@euclidean_cartesian_set R m n A B):=
  projT1 (cid (@current_cartesian_domain_maps_exists R m n A B)).
(** Source for [split]: seal the second map from the
    same proved coordinate witness, supporting Federer
    4.1.8, p. 361. *)
Definition split (R:realType) (m n:nat) (A:set (R_n R m)) (B:set (R_n R n)):
    current_domain R (m+n) (@euclidean_cartesian_set R m n A B)->
    (current_domain R m A*current_domain R n B)%type:=
  projT1 (cid (projT2 (cid (@current_cartesian_domain_maps_exists R m n A B)))).
(** Source for [laws]: both sealed maps satisfy their
    independent original block specification, supporting Federer
    4.1.8, p. 361. *)
Lemma laws (R:realType) (m n:nat) (A:set (R_n R m)) (B:set (R_n R n)):
  @is_current_cartesian_domain_maps R m n A B
    (@join R m n A B) (@split R m n A B).
Proof. exact:(projT2 (cid (projT2 (cid (@current_cartesian_domain_maps_exists R m n A B))))). Qed.
End CartesianCurrentDomain.
