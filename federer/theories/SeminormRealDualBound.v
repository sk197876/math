(** Federer (1969), 4.1.1, pp. 344–345: continuity of
    a real linear functional is equivalent to a finite bound
    by one defining seminorm. Integer constants and the printed
    one-sided notation are related to the absolute-value bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP OpenFamilyTopologyUP DirectedSeminormFamilyUP
  SeminormFamilyLinearContinuity NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_real_linear_continuity_iff]: the finite
    seminorm bound for continuous real linear functionals,
    Federer 4.1.1, p. 344, and its fixed-support application
    on p. 345. No normability of the source is assumed. *)
Theorem seminorm_real_linear_continuity_iff (R:realType) (E:lmodType R)
    (I:Type) (p:I->E->R) (O:set (set E))
    (hp:is_directed_seminorm_family p) (hO:is_seminorm_family_topology p O)
    (L:Hom E R^o):
  open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R)) L <->
  exists i C,0<=C /\ forall x,`|L x|<=C * p i x.
Proof.
have h:=@seminorm_family_linear_continuity_iff R E R^o I unit p
  (fun _:unit=>fun x:R=>`|x|) O (norm_open_family (@scalar_absolute_value_norm R))
  hp (norm_single_seminorm_directed (@scalar_absolute_value_norm R)) hO
  (norm_open_family_seminorm_laws (@scalar_absolute_value_norm R)) L.
split.
- move=>hL; exact:h.1 hL tt.
- move=>hb; apply:h.2=>j; exact:hb.
Qed.

(** Source for [linear_one_sided_seminorm_bound_iff]: the
    printed bound T<=M nu is equivalent to |T|<=M nu for a
    real linear functional, supporting Federer 4.1.1, pp. 344–345.
    The reverse bound follows by testing -phi. *)
Theorem linear_one_sided_seminorm_bound_iff (R:realType) (E:lmodType R)
    (p:E->R) (hp:is_real_seminorm p) (L:Hom E R^o) C:
  (forall x,L x<=C * p x) <-> (forall x,`|L x|<=C * p x).
Proof.
split.
- move=>hb x; rewrite ler_norml; apply/andP; split.
  + have h:=hb (-x); rewrite linearN (real_seminorm_negate hp) in h.
    by rewrite lerNl.
  + exact:hb.
- move=>hb x; exact:le_trans (ler_norm _) (hb x).
Qed.

(** Source for [seminorm_bound_integer_constant]: a finite
    nonnegative real bound can be increased to a nonnegative
    integer, supporting i,M in Federer 4.1.1, p. 345. *)
Theorem seminorm_bound_integer_constant (R:realType) (E:lmodType R)
    (p:E->R) (hp:is_real_seminorm p) (L:Hom E R^o) C:
  0<=C -> (forall x,`|L x|<=C * p x) ->
  exists M:nat,forall x,`|L x|<=M%:R * p x.
Proof.
move=>hC hb; exists (Num.bound C)=>x.
have hLarge:C<(Num.bound C)%:R:=archi_boundP hC.
have hMul:=ler_wpM2r (real_seminorm_nonnegative hp x) (ltW hLarge).
exact:(le_trans (hb x) hMul).
Qed.
