(** Federer (1969), 4.1.1, p. 343: nu^i_K is the least
    nonnegative bound of the norms of D^j f(x), for j<=i and x in K.
    This supporting specification treats any family of linear
    observations in independently normed target spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_linear_observation_seminorm]: independent
    least-bound specification for the derivative seminorms in
    Federer 4.1.1, p. 343. The existing uniform-norm specification
    supplies the zero convention for an empty observation family. *)
Definition is_linear_observation_seminorm (R:realType) (E:lmodType R)
    (I:Type) (W:I->lmodType R) (N:forall i,W i->R)
    (L:forall i,Hom E (W i)) (p:E->R) :=
  forall f,is_uniform_function_norm (fun i=>@N i (@L i f)) (p f).
