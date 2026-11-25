(** Federer (1969), 4.1.7, p. 357: the actual
    multivector dual is normed by mass, as in 1.8.1,
    p. 38. Its abstract norm laws follow from the
    released supremum laws and Euclidean comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP InnerProductUP ExteriorGrading
  AlternatingForms LinearBasis ExteriorNorm ComassUP
  MassUP MassBounds MassHomogeneity MassEuclidean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [mass_real_norm]: mass is the norm on
    the multivector dual used in Federer 4.1.7,
    p. 357. Supporting laws and the lower Euclidean
    comparison are those of 1.8.1, p. 38. *)
Theorem mass_real_norm (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) m (hm:(0<m)%N)
    (kappa:A_m V R^o m->R)
    (hk:forall phi,is_comass h2 hB phi (kappa phi))
    (N:exterior_power V m->R)
    (hN:forall xi,is_mass kappa xi (N xi)):
  is_real_norm N.
Proof.
split.
- constructor.
  + move=>xi; exact:(@mass_nonnegative R h2 V B hB m hm kappa hk xi (N xi) (hN xi)).
  + move=>a xi; exact:(@mass_absolute_homogeneity R h2 V B hB m hm
      kappa hk xi a (N xi) (N (a*:xi)) (hN xi) (hN (a*:xi))).
  + move=>xi eta; exact:(@mass_triangle R V m kappa xi eta
      (N xi) (N eta) (N (xi+eta)) (hN xi) (hN eta) (hN (xi+eta))).
- move=>xi hz.
  have hb:=@euclidean_le_mass R h2 V B hB n e he m hm kappa hk xi (N xi) (hN xi).
  rewrite hz in hb.
  have hn:=exterior_norm_nonnegative h2 hB xi.
  have heq:exterior_norm h2 hB xi=0 by apply/eqP; rewrite eq_le hb hn.
  apply/eqP; by rewrite -(exterior_norm_eq0 h2 hB xi) heq eqxx.
Qed.
