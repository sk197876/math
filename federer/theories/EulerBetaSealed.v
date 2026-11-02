(** Opaque angular B function for Federer (1969), 3.2.13,
    pp. 250–251. Downstream modules use only its independent
    sphere-integral specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations PartialFunctionUP EulerBetaUP EulerBetaConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type EulerBetaSignature.
(** Source for [value]: positive-coordinate angular B function,
    Federer 3.2.13, p. 250. *)
Parameter value:forall (R:realType) m,(0<m)%N ->partial_function (R_n R m) R.
(** Source for [laws]: proved defining integral, domain and
    positivity of B, Federer 3.2.13, pp. 250–251. *)
Parameter laws:forall (R:realType) m (hm:(0<m)%N),is_euler_beta (@value R m hm).
End EulerBetaSignature.
Module EulerBeta:EulerBetaSignature.
(** Source for [value]: an opaque proved angular-integral
    witness, Federer 3.2.13, p. 250. *)
Definition value (R:realType) m (hm:(0<m)%N):=projT1 (cid (@euler_beta_exists R m hm)).
(** Source for [laws]: the opaque witness satisfies the
    independent specification, Federer 3.2.13, pp. 250–251. *)
Lemma laws (R:realType) m (hm:(0<m)%N):is_euler_beta (@value R m hm).
Proof. exact:projT2 (cid (@euler_beta_exists R m hm)). Qed.
End EulerBeta.
