(** Federer (1969), 3.1.11, pp. 218–220:
    zeroth-order values belong to the space of zero-linear
    maps, canonically identified with Y. This identification
    uses only the abstract space laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [zero_arity_arguments_unique]: the empty
    argument family for zeroth-order forms, supporting D^0 f=f
    in Federer 3.1.11, pp. 218–220. *)
Lemma zero_arity_arguments_unique (X : Type) (u v : {ffun 'I_0->X}) : u=v.
Proof.
apply/ffunP=> i; by have := ltn_ord i; rewrite ltn0.
Qed.

Section ZeroForms.
Variable R : realType.
Variables X Y Z : lmodType R.
Variables NX : X->R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : {ffun 'I_0->X}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hZ : is_continuous_multilinear_space NX NY evaluation ZN.
Local Notation empty_arguments := ([ffun i : 'I_0=>(0:X)]).

(** Source for [continuous_multilinear_zero_injective]:
    a zero-linear form is determined by its single value,
    supporting Federer 3.1.11, pp. 218–220. *)
Lemma continuous_multilinear_zero_injective : injective (evaluation empty_arguments).
Proof.
move=> z w he; apply: (continuous_multilinear_extensional hZ)=> u.
by rewrite (zero_arity_arguments_unique u empty_arguments).
Qed.

(** Source for [continuous_multilinear_zero_surjective]:
    every value in Y is a zero-linear form, supporting
    Federer 3.1.11, pp. 218–220, without a
    nonzero-dimensionality assumption on X or Y. *)
Lemma continuous_multilinear_zero_surjective (y : Y) :
  exists z, evaluation empty_arguments z=y.
Proof.
have hf : norm_bounded_multilinear NX NY (fun _ : {ffun 'I_0->X}=>y).
  split.
  - by move=> u i; have := ltn_ord i; rewrite ltn0.
  - exists (NY y); split; first exact: (real_seminorm_nonnegative hNY.1 y).
    by move=> u; rewrite big_ord0 mulr1.
have [z hz] := continuous_multilinear_surjective hZ hf.
exists z; exact: hz.
Qed.

(** Source for [continuous_multilinear_zero_norm]: the
    zero-linear operator norm is the norm of its value,
    in the degree-zero convention for Federer 3.1.11,
    pp. 218–220. It need not be zero. *)
Lemma continuous_multilinear_zero_norm z : ZN z=NY (evaluation empty_arguments z).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ z)).
  + exact: (real_seminorm_nonnegative hNY.1 (evaluation empty_arguments z)).
  + move=> u; rewrite (zero_arity_arguments_unique u empty_arguments) big_ord0 mulr1.
    exact: lexx.
- have hh := multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) empty_arguments.
  by rewrite big_ord0 mulr1 in hh.
Qed.
End ZeroForms.
