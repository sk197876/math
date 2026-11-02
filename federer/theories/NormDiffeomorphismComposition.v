(** Federer (1969), 3.1.19, p. 231: composing straightening charts
    with linear coordinate changes. These supporting laws use only
    the abstract diffeomorphism and class specifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormRegularity NormRegularityOperations NormDiffeomorphismUP NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_spaces_isomorphic_transitive]: composition of
    bounded ambient linear isomorphisms, supporting the coordinate
    changes in Federer 3.1.19, p. 231. *)
Lemma norm_spaces_isomorphic_transitive (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R) :
  norm_spaces_isomorphic NX NY -> norm_spaces_isomorphic NY NZ ->
  norm_spaces_isomorphic NX NZ.
Proof.
move=>[L [M [hL [hM [hLM hML]]]]] [P [Q [hP [hQ [hPQ hQP]]]]].
exists (hom_comp P L),(hom_comp M Q); split; first exact: norm_bounded_linear_compose hL hP.
split; first exact: norm_bounded_linear_compose hQ hM.
split=>x; by rewrite !hom_compE ?hPQ ?hLM ?hML ?hQP.
Qed.

(** Source for [norm_diffeomorphism_composition]: the composite of
    diffeomorphisms is a diffeomorphism, supporting the chart changes
    in Federer 3.1.19, p. 231. Both actual images are preserved. *)
Lemma norm_diffeomorphism_composition (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (C:Z->Prop)
    (f:X->Y) (g:Y->X) (h:Y->Z) (q:Z->Y) k :
  is_norm_diffeomorphism hNX hNY A B f g k ->
  is_norm_diffeomorphism hNY hNZ B C h q k ->
  is_norm_diffeomorphism hNX hNZ A C (fun x=>h (f x)) (fun z=>g (q z)) k.
Proof.
move=>[hXY hf hg hfB hgA hgf hfg] [hYZ hh hq hhC hqB hqh hhq].
constructor.
- exact: norm_spaces_isomorphic_transitive hXY hYZ.
- exact (@norm_class_compose_on R X Y Z NX NY NZ hNX hNY hNZ A B f h k hfB hf hh).
- exact (@norm_class_compose_on R Z Y X NZ NY NX hNZ hNY hNX C B q g k hqB hq hg).
- move=>x hx; exact: hhC (hfB x hx).
- move=>z hz; exact: hgA (hqB z hz).
- move=>x hx; by rewrite hqh ?hgf //; exact: hfB.
- move=>z hz; by rewrite hfg ?hhq //; exact: hqB.
Qed.

(** Source for [norm_linear_diffeomorphism]: a bounded linear
    isomorphism is a diffeomorphism of every class, supporting the
    adapted-plane coordinates in Federer 3.1.19, p. 231. *)
Lemma norm_linear_diffeomorphism (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (L:Hom X Y) (M:Hom Y X) k :
  norm_bounded_linear NX NY L -> norm_bounded_linear NY NX M ->
  cancel L M -> cancel M L ->
  is_norm_diffeomorphism hNX hNY (fun _=>True) (fun _=>True) L M k.
Proof.
move=>hL hM hLM hML; constructor=>//.
- exists L,M; by split=>//; split=>//; split.
- exact (@norm_class_linear R X Y NX NY hNX hNY (fun _=>True) L k
    (fun x _=>norm_full_domain_interior NX x) hL).
- exact (@norm_class_linear R Y X NY NX hNY hNX (fun _=>True) M k
    (fun y _=>norm_full_domain_interior NY y) hM).
Qed.
