(** Federer (1969), 3.4.12, p. 339:
    original local holomorphic representatives are closed
    under the original pointwise ring operations. Choose
    common open neighbourhoods only inside the existence proofs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormLinearDomainLaws NormOpenDomainLaws
  HolomorphicUP HolomorphicOpenDomain HolomorphicArithmetic HolomorphicNegation
  HolomorphicProduct HolomorphicRestriction HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Representatives.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Local Notation C:=(ComplexScalars.C R).
Local Notation NC:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation P:=(@holomorphic_representative_type R X NX hNX a).
Local Notation value:=(@holomorphic_representative_value R X NX hNX a).
Local Notation HOL A f:=(@is_holomorphic R X C^o NX NC hNX hN A f).

(** Source for [holomorphic_representatives_common_domain]: two
    original germ representatives share an actual holomorphic
    neighbourhood, 3.4.12, p. 339. *)
Theorem holomorphic_representatives_common_domain (f g:P):
  exists U:X->Prop,U a /\HOL U (value f) /\HOL U (value g).
Proof.
have [A [ha hF]]:=holomorphic_representative_holomorphic f.
have [B [hb hG]]:=holomorphic_representative_holomorphic g.
pose U:=fun x=>A x /\B x.
have hOpen x (hx:U x):norm_domain_interior NX U x.
  exact:(@norm_domain_intersection_interior R XR NX A B x
    (@holomorphic_domain_interior R X C^o NX NC hNX hN A (value f) hF x hx.1)
    (@holomorphic_domain_interior R X C^o NX NC hNX hN B (value g) hG x hx.2)).
exists U;split;first by split.
split.
- exact:(@holomorphic_open_restriction R X C^o NX NC hNX hN A U (value f)
    (fun x hx=>hx.1) hOpen hF).
- exact:(@holomorphic_open_restriction R X C^o NX NC hNX hN B U (value g)
    (fun x hx=>hx.2) hOpen hG).
Qed.

(** Source for [holomorphic_representative_constant_law]: the
    original constant functions are holomorphic near the
    original centre, 3.4.12, p. 339. *)
Lemma holomorphic_representative_constant_law (c:C):
  exists U:X->Prop,U a /\HOL U (fun _=>c).
Proof.
exists (fun _=>True);split;first exact:I.
exact:(@holomorphic_constant R X C^o NX NC hNX hN (fun _=>True) c
  (fun x _=>@norm_full_domain_interior R XR NX x)).
Qed.

(** Source for [holomorphic_representative_add_law]: the original
    sum remains holomorphic near the same centre,
    3.4.12, p. 339. *)
Lemma holomorphic_representative_add_law (f g:P):
  exists U:X->Prop,U a /\HOL U (fun x=>value f x+value g x).
Proof.
have [U [ha [hF hG]]]:=holomorphic_representatives_common_domain f g.
exists U;split;first exact:ha;exact:holomorphic_add hF hG.
Qed.

(** Source for [holomorphic_representative_multiply_law]: the original
    product remains holomorphic near the same centre,
    3.4.12, p. 339. *)
Lemma holomorphic_representative_multiply_law (f g:P):
  exists U:X->Prop,U a /\HOL U (fun x=>value f x*value g x).
Proof.
have [U [ha [hF hG]]]:=holomorphic_representatives_common_domain f g.
exists U;split;first exact:ha;exact:holomorphic_product hF hG.
Qed.

(** Source for [holomorphic_representative_negate_law]: the original
    negative remains holomorphic near the same centre,
    3.4.12, p. 339. *)
Lemma holomorphic_representative_negate_law (f:P):
  exists U:X->Prop,U a /\HOL U (fun x=> -value f x).
Proof.
have [U [ha hF]]:=holomorphic_representative_holomorphic f.
exists U;split;first exact:ha;exact:holomorphic_negate hF.
Qed.

(** Source for [holomorphic_constant_representative]: actual
    original constant representative for the holomorphic ring,
    3.4.12, p. 339. *)
Definition holomorphic_constant_representative (c:C):P:=
  exist _ (fun _=>c) (holomorphic_representative_constant_law c).

(** Source for [holomorphic_add_representatives]: pointwise
    addition of original holomorphic representatives, 3.4.12,
    p. 339; its local regularity is proved above. *)
Definition holomorphic_add_representatives (f g:P):P:=
  exist _ (fun x=>value f x+value g x) (holomorphic_representative_add_law f g).

(** Source for [holomorphic_multiply_representatives]: pointwise
    multiplication of original holomorphic representatives,
    3.4.12, p. 339; its local regularity is proved above. *)
Definition holomorphic_multiply_representatives (f g:P):P:=
  exist _ (fun x=>value f x*value g x) (holomorphic_representative_multiply_law f g).

(** Source for [holomorphic_negate_representative]: pointwise
    negation of original holomorphic representatives, 3.4.12,
    p. 339; its local regularity is proved above. *)
Definition holomorphic_negate_representative (f:P):P:=
  exist _ (fun x=> -value f x) (holomorphic_representative_negate_law f).
End Representatives.
