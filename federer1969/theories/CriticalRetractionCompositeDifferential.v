(** Federer (1969), 3.4.2(6)–(7), pp. 312–313: differentiate the
    identity F composed with r=F, where F=f composed with r. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialChain
  NormDifferentialLocal NormDifferentialDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_retraction_composite_differential]: supporting
    the chain formula in 3.4.2(6), p. 312, and the derivative functions
    in (7), p. 313. If r preserves its domain and F composed with r=F
    there, the actual differential of F at a equals its differential
    at r(a) composed with Dr(a). This is a consequence of the chain
    rule and uniqueness, not an additional identity assumed of F. *)
Theorem critical_retraction_composite_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (r:X->X) (F:X->Y) a (Dr:Hom X X) (D E:Hom X Y):
  (forall x,U x ->U (r x)) ->(forall x,U x ->F (r x)=F x) ->
  has_norm_differential NX NX U r a Dr ->
  has_norm_differential NX NY U F a D ->
  has_norm_differential NX NY U F (r a) E ->D=hom_comp E Dr.
Proof.
move=>hMap hEqual hr hF hFr.
have hChain:=norm_differential_chain hNX hNX hNY hr hFr.
have hDomain:(fun x=>U x /\U (r x))=U.
  apply:funext=>x;apply:propext;split.
  - by move=>[].
  - move=>hx;split;[exact:hx|exact:hMap x hx].
rewrite hDomain in hChain.
have hComp:=norm_differential_domain_agreement hNX hEqual hChain.
exact:(norm_differential_unique hNX hNY hF hComp).
Qed.
