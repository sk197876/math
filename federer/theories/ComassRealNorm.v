(** Federer (1969), 4.1.7, p. 357: apply 4.1.5 with
    real covectors normed by comass. The norm laws below
    reuse the original positive-degree supremum laws of
    1.8.1, p. 38, rather than a coordinate construction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP InnerProductUP AlternatingForms
  ComassUP ComassBounds ComassHomogeneity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [comass_real_norm]: the original comass
    is a norm on the covector space used in Federer
    4.1.7, p. 357; supporting norm laws from 1.8.1,
    p. 38. Positive degree preserves the already recorded
    degree-zero qualification of that supremum. *)
Theorem comass_real_norm (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    m (hm:(0<m)%N) (N:A_m V R^o m->R)
    (hN:forall phi,is_comass h2 hB phi (N phi)):
  is_real_norm N.
Proof.
split.
- constructor.
  + move=>phi; exact:(@comass_nonnegative R h2 V B hB m phi (N phi) hm (hN phi)).
  + move=>a phi; exact:(@comass_absolute_homogeneity R h2 V B hB m hm
      phi a (N phi) (N (a*:phi)) (hN phi) (hN (a*:phi))).
  + move=>phi psi; exact:(@comass_triangle R h2 V B hB m phi psi
      (N phi) (N psi) (N (phi+psi)) (hN phi) (hN psi) (hN (phi+psi))).
- move=>phi hz; apply:(@comass_definite R h2 V B hB m hm phi).
  by rewrite -hz; exact:hN.
Qed.
