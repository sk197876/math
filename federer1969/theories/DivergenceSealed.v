(** Federer (1969), 4.1.6, p. 354: the
    original divergence map behind its proved opaque
    interface. Only the independently specified
    Hom/tensor/interior law is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom GrassmannAbbreviations ExteriorGrading DivergenceUP DivergenceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type DivergenceSignature.
(** Source for [value]: the original linear divergence
    applied to D xi(x), Federer 4.1.6, p. 354. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n p,
  Hom (Hom (R_n R n) (exterior_power (R_n R n) p.+1)) (exterior_power (R_n R n) p).
(** Source for [laws]: the original defining composite,
    Federer 4.1.6, p. 354. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n p
  (L:Hom (R_n R n) (exterior_power (R_n R n) p.+1)),
  is_divergence_value h2 L (@value R h2 n p L).
End DivergenceSignature.
Module Divergence:DivergenceSignature.
(** Source for [value]: select the proved linear map,
    Federer 4.1.6, p. 354. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n p:
    Hom (Hom (R_n R n) (exterior_power (R_n R n) p.+1)) (exterior_power (R_n R n) p):=
  projT1 (cid (@divergence_map_exists R h2 n p)).
(** Source for [laws]: the selected map has the exact
    original composite values,
    Federer 4.1.6, p. 354. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n p
    (L:Hom (R_n R n) (exterior_power (R_n R n) p.+1)):
  is_divergence_value h2 L (@value R h2 n p L).
Proof. exact:(projT2 (cid (@divergence_map_exists R h2 n p)) L). Qed.
End Divergence.
