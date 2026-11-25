(** Federer (1969), 4.1.1, pp. 343–344: E(U,Y) is the vector
    space of all class-infinity functions from U to Y. Evaluation
    specifies this space independently of a subtype construction.
    Total evaluation representatives are zero outside U; no value
    there belongs to the mathematical function on U. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_smooth_function_space]: independent realization
    laws for E(U,Y), Federer 4.1.1, pp. 343–344. Evaluation respects
    vector operations, represents precisely the smooth functions on
    U, and identifies equal functions. *)
Record is_smooth_function_space (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y) : Prop := {
  (** Source for [smooth_function_evaluation_linear]: pointwise
      vector operations in E(U,Y), Federer 4.1.1, p. 343. *)
  smooth_function_evaluation_linear : forall c f g x,
    ev (c*:f+g) x=c*:ev f x+ev g x;
  (** Source for [smooth_function_evaluation_smooth]: every member
      of E(U,Y) has every finite class on U, Federer 4.1.1, p. 343. *)
  smooth_function_evaluation_smooth : forall f,
    norm_class_all_orders hNX hNY U (ev f);
  (** Source for [smooth_function_evaluation_outside]: a harmless
      total-representative convention supporting the actual-domain
      definition of E(U,Y), Federer 4.1.1, p. 343. *)
  smooth_function_evaluation_outside : forall f x, ~U x -> ev f x=0;
  (** Source for [smooth_function_evaluation_injective]: functions
      with the same values are equal, Federer 4.1.1, p. 343. *)
  smooth_function_evaluation_injective : injective ev;
  (** Source for [smooth_function_evaluation_surjective]: every
      smooth function on U is represented in E(U,Y), Federer
      4.1.1, p. 343. Values outside U are not prescribed. *)
  smooth_function_evaluation_surjective : forall f:X->Y,
    norm_class_all_orders hNX hNY U f -> exists g,
    forall x,U x -> ev g x=f x
}.
