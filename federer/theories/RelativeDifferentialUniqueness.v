(** Federer (1969), 3.1.22, p. 235: independence of
    the relative differential from its ambient differentiable extension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP PartialFunctionUP PartialFunctionExtensionality
  TangentConeUP RelativeDifferentialUP NormVanishingTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [relative_norm_differential_unique]: the
    uniqueness justified by the opening vanishing-on-S observation
    in Federer 3.1.22, p. 235. Only values on
    the tangent cone are compared; different ambient differentials
    can represent the same relative differential. *)
Theorem relative_norm_differential_unique (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:X->Prop) (f:X->Y) a (L M:partial_function X Y) :
  @has_relative_norm_differential R X Y NX NY hNX A S f a L ->
  @has_relative_norm_differential R X Y NX NY hNX A S f a M -> L=M.
Proof.
move=>[hcl [U [g [D [hg [hfg hDL]]]]]] [_ [V [h [E [hh [hfh hEM]]]]]].
have hgh x (hxS:S x) (hxU:U x) (hxV:V x):g x=h x.
  exact (eq_trans (esym (hfg x hxS hxU).2) (hfh x hxS hxV).2).
have hDE:=@norm_differentials_agree_on_tangent R X Y NX NY hNX hNY U V S g h a D E
  hg hh hcl hgh.
apply: partial_function_graph_extensionality=>v y; split=>hy.
- have [hv he]:=(hDL v y).1 hy.
  apply: (hEM v y).2; split=>//.
  exact (eq_trans (esym (hDE v hv)) he).
- have [hv he]:=(hEM v y).1 hy.
  apply: (hDL v y).2; split=>//.
  exact (eq_trans (hDE v hv) he).
Qed.
