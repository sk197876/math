(** Federer (1969), 4.1.1, pp. 344–345: existence of the
    abstract subspace carriers, reusing the algebraic carrier
    already established for 1.6.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [linear_subspace_representation_exists]: an actual
    injective linear model of every specified subspace, supporting
    the function and dual spaces of Federer 4.1.1, pp. 344–345.
    The earlier subtype construction serves only as this witness. *)
Theorem linear_subspace_representation_exists (K:fieldType)
    (V:lmodType K) (S:subspace V) :
  exists W:lmodType K,exists inc:Hom W V,
    is_linear_subspace_representation S inc.
Proof.
pose W:=GRing.Lmodule.clone K (subspace_space S) _.
pose inc:Hom W V:=@HomMap K W V (@subspace_val K V S)
  (introT (asboolP _) (@subspace_val_linear K V S)).
exists W,inc; constructor.
- exact:subspace_val_injective.
- exact:subspace_valP.
- move=>v hv; exists (subspace_lift hv); exact:subspace_liftE.
Qed.
