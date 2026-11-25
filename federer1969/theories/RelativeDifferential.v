(** Federer (1969), 3.1.22, p. 235: public exact
    relative differential interface, using only the opaque laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP RelativeDifferentialUP RelativeDifferentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_norm_differential]: the notation Df(a)
    relative to S in Federer 3.1.22, p. 235.
    The value at a, when defined, is itself a partial
    function on exactly Tan(S,a). *)
Definition relative_norm_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) :=
  @RelativeNormDifferential.value R X Y NX NY hNX hNY A S f.

(** Source for [relative_norm_differential_graph]: the exact
    graph law for the relative Df(a) of Federer 3.1.22,
    p. 235, with no default values off its differentiability locus. *)
Lemma relative_norm_differential_graph (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) a L :
  partial_function_graph (@relative_norm_differential R X Y NX NY hNX hNY A S f) a L <->
    @has_relative_norm_differential R X Y NX NY hNX A S f a L.
Proof. exact (@RelativeNormDifferential.laws R X Y NX NY hNX hNY A S f a L). Qed.

(** Source for [relative_norm_differential_domain]: the partial
    domain of Df relative to S, Federer 3.1.22,
    p. 235, consists exactly of relative-differentiability points. *)
Lemma relative_norm_differential_domain (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) :
  partial_function_domain (@relative_norm_differential R X Y NX NY hNX hNY A S f)=
    [set a|@relative_norm_differentiable_at R X Y NX NY hNX A S f a].
Proof.
apply/seteqP; split=>a [L hL]; exists L.
- exact ((@relative_norm_differential_graph R X Y NX NY hNX hNY A S f a L).1 hL).
- exact ((@relative_norm_differential_graph R X Y NX NY hNX hNY A S f a L).2 hL).
Qed.
