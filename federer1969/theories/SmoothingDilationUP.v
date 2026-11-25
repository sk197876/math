(** Federer (1969), 4.1.2, p. 346: the
    exact positive-scale dilation of the original kernel.
    The formula is specified independently of a selected
    implementation and of the later support and integral proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_smoothing_dilation]: Phi_epsilon(x) equals
    epsilon^(-n) Phi(epsilon^(-1)x) for positive epsilon,
    the first definition in Federer 4.1.2, p. 346.
    Values at nonpositive scales are not prescribed. *)
Definition is_smoothing_dilation (R:realType) n (phi:R_n R n->R)
    (family:R->R_n R n->R):=
  forall e:R,0<e ->forall x,family e x=(e^+n)^-1*phi (e^-1*:x).

(** Source for [smoothing_dilation_positive_unique]: the
    original formula determines every positive-scale value,
    supporting the family in Federer 4.1.2, p. 346. *)
Lemma smoothing_dilation_positive_unique (R:realType) n (phi:R_n R n->R) a b:
  is_smoothing_dilation phi a ->is_smoothing_dilation phi b ->
  forall e:R,0<e ->forall x,a e x=b e x.
Proof. move=>ha hb e he x; by rewrite (ha e he x) (hb e he x). Qed.
