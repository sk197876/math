(** Supporting Federer (1969), 3.4.8(5), p. 328:
    existence and uniqueness of the original vanishing
    ideal, specified independently by centre-value laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticGermValueSealed AnalyticVanishingIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_vanishing_ideal_exists]: the centre
    value supplies an existence witness for the
    original local ideal used in 3.4.7, p. 325,
    and the closedness proof for 3.4.8(5), p. 328. *)
Theorem analytic_vanishing_ideal_exists (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a:
  exists I:set (@analytic_germ_ring R X NX hNX a),is_analytic_vanishing_ideal I.
Proof.
exists (fun alpha=>@AnalyticGermValue.map R X NX hNX a alpha = 0%R).
by move=>alpha;split.
Qed.

(** Source for [analytic_vanishing_ideal_unique]: the original
    centre-value laws uniquely determine the local ideal,
    supporting the same arguments, pp. 325, 328. *)
Lemma analytic_vanishing_ideal_unique (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a (I J:set (@analytic_germ_ring R X NX hNX a)):
  is_analytic_vanishing_ideal I ->is_analytic_vanishing_ideal J ->I = J.
Proof. move=>hI hJ;apply/seteqP;split=>alpha ha;[apply/(hJ alpha);apply/(hI alpha)|apply/(hI alpha);apply/(hJ alpha)];exact:ha. Qed.
