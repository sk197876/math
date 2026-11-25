(** Federer (1969), 4.1.2, pp. 346–347:
    an invertible argument dilation does not change the
    range of the derivative norm. This supporting law
    uses only the earlier least-bound norm specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [uniform_function_norm_surjective_precompose]:
    surjective change of argument preserves the exact
    uniform norm, supporting the dilation equality in
    Federer 4.1.2, pp. 346–347. *)
Lemma uniform_function_norm_surjective_precompose (R:realType) (X Y:Type)
    (f:Y->R) (T:X->Y) n:(forall y:Y,exists x:X,T x=y) ->is_uniform_function_norm f n ->
  is_uniform_function_norm (fun x=>f (T x)) n.
Proof.
move=>hT hn; constructor.
- exact:uniform_function_norm_nonnegative hn.
- move=>x; exact:uniform_function_norm_bound hn (T x).
- move=>c hc hBound; apply:(uniform_function_norm_least hn hc)=>y.
  have [x <-]:=hT y; exact:hBound x.
Qed.
