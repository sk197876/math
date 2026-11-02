(** Federer (1969), 3.2.9, p. 247: the
    kernel of an epimorphism R^(n+k) to R^n
    has dimension k. Specify a kernel frame
    by independence and exact spanning before proving
    its existence from the sealed linear chart. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteIndependence FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_euclidean_kernel_frame]: the
    finite-dimensional kernel in the first paragraph
    of the proof of Federer 3.2.9, p. 247.
    A frame is independent and spans exactly
    the vectors annihilated by the actual linear map.
    The source dimension n+k represents m with n<=m. *)
Definition is_euclidean_kernel_frame (R:realType) n k
    (L:Hom (R_n R (n+k)) (R_n R n)) (e:'I_k->R_n R (n+k)):Prop:=
  finite_independent e /\ forall x,L x=0 <-> in_finite_span e x.
