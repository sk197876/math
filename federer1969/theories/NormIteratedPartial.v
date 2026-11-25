(** Federer (1969), 3.1.11, p. 223: ordered higher
    coordinate partial derivatives, through the sealed recursive graph. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP PartialFunctionUP GrassmannAbbreviations
  FiniteCoordinates NormIteratedDirectionalUP NormIteratedDirectionalSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_iterated_partial]: D_nu f, obtained
    by successively differentiating in the listed coordinate directions,
    Federer 3.1.11, p. 223. The sequence is ordered:
    its first entry is the outermost derivative. *)
Definition norm_iterated_partial (R : realType) n (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R_n R n->Prop) (f : R_n R n->Y) (nu : seq 'I_n) :
    partial_function (R_n R n) Y :=
  @NormIteratedDirectional.value R (R_n R n) Y NY hNY A f
    [seq (@coordinate_basis R n) i | i <- nu].

(** Source for [norm_iterated_partial_graph]: the exact
    recursive graph law for D_nu f, Federer 3.1.11,
    p. 223. Every intermediate derivative uses its own domain. *)
Lemma norm_iterated_partial_graph (R : realType) n (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R_n R n->Prop) (f : R_n R n->Y) (nu : seq 'I_n) a y :
  partial_function_graph (norm_iterated_partial hNY A f nu) a y <->
    has_norm_iterated_directional NY A f
      [seq (@coordinate_basis R n) i | i <- nu] a y.
Proof. exact: NormIteratedDirectional.laws. Qed.
