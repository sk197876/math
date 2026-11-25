(** Federer (1969), 4.1.14, pp. 370–371: changing the
    chosen neighbourhood or evidence of compactness does not
    change a compact index with the same actual carrier.
    This supporting law concerns the existing independent
    compact-set record of 4.1.1, p. 343. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [smooth_compact_set_extensionality]: equal
    original compact carriers give the same compact index,
    supporting the neighbourhood independence in Federer
    4.1.14, pp. 370–371. The proof fields are propositions. *)
Lemma smooth_compact_set_extensionality (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (K L:smooth_compact_set hNX U):
  smooth_compact_carrier K=smooth_compact_carrier L ->K=L.
Proof.
case:K=>K hK cK;case:L=>L hL cL /= hEquality;subst L.
have ->:hK=hL:=Prop_irrelevance _ _.
have ->:cK=cL:=Prop_irrelevance _ _.
by [].
Qed.
