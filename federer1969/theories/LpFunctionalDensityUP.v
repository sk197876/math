(** Federer (1969), 2.5.7, p. 98: a representing density k belongs to Lq and
    satisfies mu(f)=integral f*k for every total f in Lp. Erratum p. 2, book
    p. 98 line 10, specifies the total-domain space. This predicate
    specifies the density by its laws, independently of the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import TotalScalarLpUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_lp_functional_density]: the direct representing- density
    specification in Federer 2.5.7, p. 98 The product integral must actually
    exist with the specified finite value; arbitrary values of a totalized
    integral are not used to state the representation. *)
Definition is_lp_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) p q (A : (X -> R) -> R) (k : X -> R) :=
  total_scalar_lp mu q k /\ forall f, total_scalar_lp mu p f ->
    is_measure_integral mu (real_total_integrand (fun x => (f x*k x)%R)) (A f)%:E.
