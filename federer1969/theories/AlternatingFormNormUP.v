(** Federer (1969), 4.1.6, p. 352: the induced norm
    on alternating forms is the original multilinear
    operator norm of 3.1.11, p. 219. The independent
    least-bound laws determine it before its existence
    witness or opaque choice is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP AlternatingForms AlternatingFormNormBound ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_alternating_form_norm]: the actual
    induced norm specified in Federer 4.1.6, p. 352,
    with the corrected target-norm supremum of 3.1.11,
    p. 219 (erratum book p. 219 line 4). *)
Definition is_alternating_form_norm (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) m (N:A_m V W m->R):Prop:=
  forall phi,is_multilinear_operator_norm NV NW (form_ordered_value phi) (N phi).
