(** Federer (1969), 3.1.24, p. 239: the
    scalar rational function used to evaluate the composition
    coefficient sum, with its actual domain recorded. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import TensorUP SymmetricForms SymmetricFunctionalProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_fraction_domain]: the nonzero
    denominator condition for cx/(1-cx) in Federer 3.1.24,
    p. 239. The denominator is written as (-c)x+1
    to match the existing affine substitution laws. *)
Definition scalar_analytic_fraction_domain (R:realType) (c x:R) :=-c*x+1!=0.

(** Source for [scalar_analytic_fraction]: f(x)=cx/(1-cx)
    in Federer 3.1.24, p. 239. The equivalent
    reciprocal-minus-one expression allows direct use of the
    proved reciprocal differential fields; assertions use its
    explicit nonzero-denominator domain. *)
Definition scalar_analytic_fraction (R:realType) (c x:R) :=(-c*x+1)^-1-1.

(** Source for [scalar_analytic_fraction_value]: supporting
    agreement with the printed formula cx/(1-cx), Federer
    3.1.24, p. 239, on its actual domain. *)
Lemma scalar_analytic_fraction_value (R:realType) (c x:R) :
  scalar_analytic_fraction_domain c x -> scalar_analytic_fraction c x= c*x/(1-c*x).
Proof.
rewrite /scalar_analytic_fraction_domain /scalar_analytic_fraction.
have he:-c*x+1= 1-c*x by ring.
rewrite he=>h; field; exact h.
Qed.

(** Source for [scalar_analytic_fraction_zero_domain]: the
    origin belongs to the domain of the scalar rational
    function in Federer 3.1.24, p. 239, for every
    finite parameter c, including c=0. *)
Lemma scalar_analytic_fraction_zero_domain (R:realType) (c:R) :
  scalar_analytic_fraction_domain c 0.
Proof. by rewrite /scalar_analytic_fraction_domain mulr0 add0r oner_eq0. Qed.

(** Source for [scalar_analytic_fraction_zero]: the scalar
    special case in Federer 3.1.24, p. 239,
    satisfies f(0)=0, so the outer derivatives are also
    evaluated at the origin. *)
Lemma scalar_analytic_fraction_zero (R:realType) (c:R) :scalar_analytic_fraction c 0= 0.
Proof. by rewrite /scalar_analytic_fraction mulr0 add0r invr1 subrr. Qed.

(** Source for [scalar_analytic_fraction_form]: the derivatives
    at zero of cx/(1-cx) in Federer 3.1.24,
    p. 239. Positive orders are c^j j! times
    the product form, and order zero is zero. That
    these candidates are actual derivatives is proved separately. *)
Definition scalar_analytic_fraction_form (R:realType) (c:R) j:S_m R^o R^o j :=
  match j as k return S_m R^o R^o k with
  | 0%N=>0
  | k.+1=>(c^+k.+1*((k.+1)`!)%:R)*:symmetric_functional_product_form (linear_id R^o) k.+1
  end.
