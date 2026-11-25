(** Federer (1969), 4.1.18, p. 375: equality
    identifies original smooth-form spaces on equal
    open domains. The point values and exterior
    differential are unchanged. This adapter introduces
    no new smooth representative or axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCurrentExteriorDerivative CurrentEqualDomainTests SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_smooth_equal_domain]: exact
    equality of the original smooth coefficient
    spaces, supporting 4.1.18, p. 375. *)
Definition current_smooth_equal_domain (R:realType) (h2:(1+1:R)!= 0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U= V):
    Hom (@current_smooth_space R h2 n U hU m) (@current_smooth_space R h2 n V hV m).
Proof.
destruct e.
exact:(eq_rect_r
  (fun hV=>Hom (@current_smooth_space R h2 n U hU m)
    (@current_smooth_space R h2 n U hV m))
  (hom_of_linear (@linear_id R (@current_smooth_space R h2 n U hU m)))
  (Prop_irrelevance hV hU)).
Defined.

(** Source for [current_smooth_equal_domain_values]:
    the actual original form coefficients are
    unchanged, supporting 4.1.18, p. 375. *)
Theorem current_smooth_equal_domain_values (R:realType) (h2:(1+1:R)!= 0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U= V) (omega:@current_smooth_space R h2 n U hU m) x:
  @current_smooth_value R h2 n V hV m
    (@current_smooth_equal_domain R h2 n m U V hU hV e omega) x=
  @current_smooth_value R h2 n U hU m omega x.
Proof.
destruct e;have hProof:hV= hU:=Prop_irrelevance _ _;subst hV.
rewrite /current_smooth_equal_domain.
rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.

(** Source for [current_smooth_equal_domain_exterior_derivative]:
    the same original exterior derivative survives
    equality of domain presentations, supporting
    the form homotopy of 4.1.18, p. 375. *)
Theorem current_smooth_equal_domain_exterior_derivative
    (R:realType) (h2:(1+1:R)!= 0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U= V) (omega:@current_smooth_space R h2 n U hU m):
  @smooth_current_exterior_derivative R h2 n m V hV
    (@current_smooth_equal_domain R h2 n m U V hU hV e omega)=
  @current_smooth_equal_domain R h2 n m.+1 U V hU hV e
    (@smooth_current_exterior_derivative R h2 n m U hU omega).
Proof.
destruct e;have hProof:hV= hU:=Prop_irrelevance _ _;subst hV.
rewrite /current_smooth_equal_domain.
rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.

(** Source for [current_smooth_equal_domain_test_inclusion]:
    equality of domain presentations preserves the
    actual compact-test inclusion, supporting the
    test-form homotopy of 4.1.18, p. 375. *)
Theorem current_smooth_equal_domain_test_inclusion
    (R:realType) (h2:(1+1:R)!= 0) n m
    (U V:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall x,V x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (e:U= V) (omega:@current_test_space R h2 n U hU m):
  @current_smooth_equal_domain R h2 n m U V hU hV e
    (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU m) omega)=
  smooth_test_inclusion (@current_smooth_space_laws R h2 n V hV m)
    (@current_test_equal_domain R h2 n m U V hU hV e omega).
Proof.
destruct e;have hProof:hV= hU:=Prop_irrelevance _ _;subst hV.
rewrite /current_smooth_equal_domain /current_test_equal_domain.
rewrite (Prop_irrelevance (Prop_irrelevance hU hU) (erefl hU)).
reflexivity.
Qed.
