(** Opaque positive-domain Euler Gamma for Federer (1969),
    3.2.13, pp. 250–251. Only this sealing
    module and the assumptions audit may import the
    private existence witness. *)
From mathcomp Require Import all_boot boolp reals.
From Federer Require Import PartialFunctionUP EulerGammaUP EulerGammaConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type EulerGammaSignature.
(** Source for [value]: the function specified by its
    defining positive-ray integral, Federer 3.2.13, p. 250. *)
Parameter value:forall R:realType,partial_function R R.
(** Source for [laws]: the proved defining graph,
    existence and positivity laws, Federer 3.2.13, p. 250. *)
Parameter laws:forall R:realType,is_euler_gamma (@value R).
End EulerGammaSignature.
Module EulerGamma:EulerGammaSignature.
(** Source for [value]: an opaque witness of the
    finite positive defining integral of Federer 3.2.13, p. 250. *)
Definition value (R:realType):=projT1 (cid (@euler_gamma_exists R)).
(** Source for [laws]: the selected witness satisfies
    the independent defining laws, Federer 3.2.13, p. 250. *)
Lemma laws (R:realType):is_euler_gamma (@value R).
Proof. exact:projT2 (cid (@euler_gamma_exists R)). Qed.
End EulerGamma.
