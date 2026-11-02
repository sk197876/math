(** Federer (1969), 3.1.20, p. 232: abstract specification of
    one retraction-patching step. The corrected intermediate maps
    take values in B and fix B intersect their actual open domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormRegularity LocalRetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [retraction_patch_domain]: W_i in the induction
    of Federer 3.1.20, p. 232, with the inverse image taken inside
    the actual old domain W. P is closed and Q is open. *)
Definition retraction_patch_domain (X:Type) (W T P Q:set X) (f:X->X) :=
  (W `\` P) `|` [set x|W x /\ T x /\ T (f x)] `|` Q.

(** Source for [is_retraction_patch]: the domain, value and
    fixed-point laws required of the new map f_i in Federer
    3.1.20, p. 232. Existence is proved separately; the invariant
    follows the erratum p. 4, book p. 232 line 11. *)
Record is_retraction_patch (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (B W T P Q:set X)
    (f rho h:X->X) k : Prop := {
  (** Source for [retraction_patch_partial]: the corrected map
      W_i to B fixes B intersect W_i, 3.1.20, p. 232. *)
  retraction_patch_partial : is_partial_neighbourhood_retraction hNX B
    (retraction_patch_domain W T P Q f) h k;
  (** Source for [retraction_patch_old_values]: f_i agrees with
      f_(i-1) away from P_i, Federer 3.1.20, p. 232. *)
  retraction_patch_old_values : forall x, W x -> ~P x -> h x=f x;
  (** Source for [retraction_patch_new_values]: f_i is the new
      local coordinate retraction on Q_i, 3.1.20, p. 232. *)
  retraction_patch_new_values : forall x, Q x -> h x=rho x;
  (** Source for [retraction_patch_membership_off]: the domain
      changes only inside P_i, supporting stabilization on p. 233
      in Federer 3.1.20. *)
  retraction_patch_membership_off : forall x, ~P x ->
    (retraction_patch_domain W T P Q f x <-> W x);
  (** Source for [retraction_patch_fixed_set]: B intersect W_i
      equals B intersect (W_(i-1) union Q_i), the displayed identity
      in Federer 3.1.20, p. 232. *)
  retraction_patch_fixed_set : B `&` retraction_patch_domain W T P Q f = B `&` (W `|` Q)
}.
